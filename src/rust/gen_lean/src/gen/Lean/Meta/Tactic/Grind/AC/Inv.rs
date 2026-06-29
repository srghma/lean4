// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Inv
// Imports: Lean.Meta.Tactic.Grind.AC.Util Lean.Meta.Tactic.Grind.AC.Seq
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Init::Grind::AC::l_Lean_Grind_AC_instBEqSeq_beq;
use crate::r#gen::Init::Prelude::l_instInhabitedForall___redArg___lam__0___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Seq::{
    initialize_Lean_Meta_Tactic_Grind_AC_Seq, l_Lean_Grind_AC_Seq_compare,
    l_Lean_Grind_AC_Seq_contains, l_Lean_Grind_AC_Seq_isSorted,
    l_Lean_Grind_AC_Seq_noAdjacentDuplicates, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Util::{
    initialize_Lean_Meta_Tactic_Grind_AC_Util, l_Lean_Meta_Grind_AC_ACM_getStruct,
    l_Lean_Meta_Grind_AC_get_x27___redArg, l_Lean_Meta_Grind_AC_hasNeutral,
    l_Lean_Meta_Grind_AC_isCommutative, l_Lean_Meta_Grind_AC_isIdempotent,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_instInhabitedGoalM;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value: crate::leanh::LeanStringObject<70> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value: crate::leanh::LeanStringObject<184> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 184, m_capacity: 184, m_length: 183, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 47, 45, 10, 42, 42, 78, 111, 116, 101, 42, 42, 58, 32, 69, 108, 101, 109, 101, 110, 116, 115, 32, 105, 110, 32, 116, 104, 101, 32, 116, 111, 100, 111, 32, 113, 117, 101, 117, 101, 32, 97, 114, 101, 32, 110, 111, 116, 32, 102, 117, 108, 108, 121, 32, 115, 105, 109, 112, 108, 105, 102, 105, 101, 100, 46, 10, 82, 101, 99, 97, 108, 108, 32, 116, 104, 97, 116, 32, 119, 101, 32, 111, 110, 108, 121, 32, 40, 102, 117, 108, 108, 121, 41, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 104, 101, 109, 32, 119, 104, 101, 110, 32, 97, 100, 100, 105, 110, 103, 32, 116, 104, 101, 109, 32, 116, 111, 32, 116, 104, 101, 32, 98, 97, 115, 105, 115, 46, 10, 45, 47, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value: crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 83, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 110, 111, 65, 100, 106, 97, 99, 101, 110, 116, 68, 117, 112, 108, 105, 99, 97, 116, 101, 115, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 115, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 48, 32, 124, 124, 32, 115, 32, 61, 61, 32, 46, 118, 97, 114, 32, 48, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 66, 97, 115, 105, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 111, 109, 112, 97, 114, 101, 32, 99, 46, 108, 104, 115, 32, 99, 46, 114, 104, 115, 32, 61, 61, 32, 46, 103, 116, 10, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_1838_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(
    mut v_msg_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472__overap_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0);
    v___f_1853_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1853_, 0, v___x_1852_);
    v___x_5472__overap_1854_ = lean_panic_fn_borrowed(v___f_1853_, v_msg_1839_);
    crate::leanh::lean_dec_ref(v___f_1853_);
    crate::leanh::lean_inc(v___y_1850_);
    crate::leanh::lean_inc_ref(v___y_1849_);
    crate::leanh::lean_inc(v___y_1848_);
    crate::leanh::lean_inc_ref(v___y_1847_);
    crate::leanh::lean_inc(v___y_1846_);
    crate::leanh::lean_inc_ref(v___y_1845_);
    crate::leanh::lean_inc(v___y_1844_);
    crate::leanh::lean_inc_ref(v___y_1843_);
    crate::leanh::lean_inc(v___y_1842_);
    crate::leanh::lean_inc(v___y_1841_);
    crate::leanh::lean_inc(v___y_1840_);
    v___x_1855_ = crate::leanh::lean_apply_12(
        v___x_5472__overap_1854_,
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
        v___y_1850_,
        crate::leanh::lean_box(0),
    );
    return v___x_1855_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___boxed(
    mut v_msg_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
    crate::leanh::lean_dec(v___y_1867_);
    crate::leanh::lean_dec_ref(v___y_1866_);
    crate::leanh::lean_dec(v___y_1865_);
    crate::leanh::lean_dec_ref(v___y_1864_);
    crate::leanh::lean_dec(v___y_1863_);
    crate::leanh::lean_dec_ref(v___y_1862_);
    crate::leanh::lean_dec(v___y_1861_);
    crate::leanh::lean_dec_ref(v___y_1860_);
    crate::leanh::lean_dec(v___y_1859_);
    crate::leanh::lean_dec(v___y_1858_);
    crate::leanh::lean_dec(v___y_1857_);
    return v_res_1869_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_1870_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(
    mut v_msg_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490__overap_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0);
    v___f_1885_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1885_, 0, v___x_1884_);
    v___x_5490__overap_1886_ = lean_panic_fn_borrowed(v___f_1885_, v_msg_1871_);
    crate::leanh::lean_dec_ref(v___f_1885_);
    crate::leanh::lean_inc(v___y_1882_);
    crate::leanh::lean_inc_ref(v___y_1881_);
    crate::leanh::lean_inc(v___y_1880_);
    crate::leanh::lean_inc_ref(v___y_1879_);
    crate::leanh::lean_inc(v___y_1878_);
    crate::leanh::lean_inc_ref(v___y_1877_);
    crate::leanh::lean_inc(v___y_1876_);
    crate::leanh::lean_inc_ref(v___y_1875_);
    crate::leanh::lean_inc(v___y_1874_);
    crate::leanh::lean_inc(v___y_1873_);
    crate::leanh::lean_inc(v___y_1872_);
    v___x_1887_ = crate::leanh::lean_apply_12(
        v___x_5490__overap_1886_,
        v___y_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
        v___y_1877_,
        v___y_1878_,
        v___y_1879_,
        v___y_1880_,
        v___y_1881_,
        v___y_1882_,
        crate::leanh::lean_box(0),
    );
    return v___x_1887_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___boxed(
    mut v_msg_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
    crate::leanh::lean_dec(v___y_1899_);
    crate::leanh::lean_dec_ref(v___y_1898_);
    crate::leanh::lean_dec(v___y_1897_);
    crate::leanh::lean_dec_ref(v___y_1896_);
    crate::leanh::lean_dec(v___y_1895_);
    crate::leanh::lean_dec_ref(v___y_1894_);
    crate::leanh::lean_dec(v___y_1893_);
    crate::leanh::lean_dec_ref(v___y_1892_);
    crate::leanh::lean_dec(v___y_1891_);
    crate::leanh::lean_dec(v___y_1890_);
    crate::leanh::lean_dec(v___y_1889_);
    return v_res_1901_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2;
    v___x_1906_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1907_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1908_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1;
    v___x_1909_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_1910_ = l_mkPanicMessageWithDecl(
        v___x_1909_,
        v___x_1908_,
        v___x_1907_,
        v___x_1906_,
        v___x_1905_,
    );
    return v___x_1910_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4;
    v___x_1913_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1914_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_1915_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1;
    v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_1917_ = l_mkPanicMessageWithDecl(
        v___x_1916_,
        v___x_1915_,
        v___x_1914_,
        v___x_1913_,
        v___x_1912_,
    );
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(
    mut v_vars_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
    mut v_____s_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1938_ = crate::leanh::lean_ctor_get(v_x_1919_, 0);
                v_snd_1939_ = crate::leanh::lean_ctor_get(v_x_1919_, 1);
                v_size_1940_ = crate::leanh::lean_ctor_get(v_vars_1918_, 2);
                v___x_1941_ = lean_nat_dec_lt(v_snd_1939_, v_size_1940_);
                if v___x_1941_ == 0 {
                    v___x_1942_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3);
                    v___x_1943_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_1942_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
                    if crate::leanh::lean_obj_tag(v___x_1943_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1943_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_1944_ = crate::leanh::lean_ctor_get(v___x_1943_, 0);
                        v_isSharedCheck_1951_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1943_)) as u8;
                        if v_isSharedCheck_1951_ == 0 {
                            v___x_1946_ = v___x_1943_;
                            v_isShared_1947_ = v_isSharedCheck_1951_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1944_);
                            crate::leanh::lean_dec(v___x_1943_);
                            v___x_1946_ = crate::leanh::lean_box(0);
                            v_isShared_1947_ = v_isSharedCheck_1951_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1952_ = l_Lean_instInhabitedExpr;
                    v___x_1953_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1952_,
                        v_vars_1918_,
                        v_snd_1939_,
                    );
                    v___x_1954_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_1938_,
                            v___x_1953_,
                        );
                    crate::leanh::lean_dec(v___x_1953_);
                    if v___x_1954_ == 0 {
                        v___x_1955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5);
                        v___x_1956_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v___x_1955_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
                        return v___x_1956_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1934_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1935_ = lean_nat_add(v_____s_1920_, v___x_1934_);
                v___x_1936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1935_);
                v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
                return v___x_1937_;
            }
            2 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(
    mut v_vars_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
    mut v_____s_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(
            v_vars_1957_,
            v_x_1958_,
            v_____s_1959_,
            v___y_1960_,
            v___y_1961_,
            v___y_1962_,
            v___y_1963_,
            v___y_1964_,
            v___y_1965_,
            v___y_1966_,
            v___y_1967_,
            v___y_1968_,
            v___y_1969_,
            v___y_1970_,
        );
    crate::leanh::lean_dec(v___y_1970_);
    crate::leanh::lean_dec_ref(v___y_1969_);
    crate::leanh::lean_dec(v___y_1968_);
    crate::leanh::lean_dec_ref(v___y_1967_);
    crate::leanh::lean_dec(v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v___y_1964_);
    crate::leanh::lean_dec_ref(v___y_1963_);
    crate::leanh::lean_dec(v___y_1962_);
    crate::leanh::lean_dec(v___y_1961_);
    crate::leanh::lean_dec(v___y_1960_);
    crate::leanh::lean_dec(v_____s_1959_);
    crate::leanh::lean_dec_ref(v_x_1958_);
    crate::leanh::lean_dec_ref(v_vars_1957_);
    return v_res_1972_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(
    mut v_f_1973_: *mut crate::leanh::LeanObject,
    mut v_s_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_b_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v_a_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v_a_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1989_, 0, v_a_1975_);
                crate::leanh::lean_ctor_set(v___x_1989_, 1, v_b_1976_);
                crate::leanh::lean_inc(v___y_1987_);
                crate::leanh::lean_inc_ref(v___y_1986_);
                crate::leanh::lean_inc(v___y_1985_);
                crate::leanh::lean_inc_ref(v___y_1984_);
                crate::leanh::lean_inc(v___y_1983_);
                crate::leanh::lean_inc_ref(v___y_1982_);
                crate::leanh::lean_inc(v___y_1981_);
                crate::leanh::lean_inc_ref(v___y_1980_);
                crate::leanh::lean_inc(v___y_1979_);
                crate::leanh::lean_inc(v___y_1978_);
                crate::leanh::lean_inc(v___y_1977_);
                v___x_1990_ = crate::leanh::lean_apply_14(
                    v_f_1973_,
                    v___x_1989_,
                    v_s_1974_,
                    v___y_1977_,
                    v___y_1978_,
                    v___y_1979_,
                    v___y_1980_,
                    v___y_1981_,
                    v___y_1982_,
                    v___y_1983_,
                    v___y_1984_,
                    v___y_1985_,
                    v___y_1986_,
                    v___y_1987_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                    v_a_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                    v_isSharedCheck_2017_ = (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_1993_ = v___x_1990_;
                        v_isShared_1994_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1991_);
                        crate::leanh::lean_dec(v___x_1990_);
                        v___x_1993_ = crate::leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2018_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                    v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2020_ = v___x_1990_;
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2018_);
                        crate::leanh::lean_dec(v___x_1990_);
                        v___x_2020_ = crate::leanh::lean_box(0);
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1991_) == 0 {
                    v_a_1995_ = crate::leanh::lean_ctor_get(v_a_1991_, 0);
                    v_isSharedCheck_2005_ = (!crate::leanh::lean_is_exclusive(v_a_1991_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1997_ = v_a_1991_;
                        v_isShared_1998_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1995_);
                        crate::leanh::lean_dec(v_a_1991_);
                        v___x_1997_ = crate::leanh::lean_box(0);
                        v_isShared_1998_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2006_ = crate::leanh::lean_ctor_get(v_a_1991_, 0);
                    v_isSharedCheck_2016_ = (!crate::leanh::lean_is_exclusive(v_a_1991_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2008_ = v_a_1991_;
                        v_isShared_2009_ = v_isSharedCheck_2016_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2006_);
                        crate::leanh::lean_dec(v_a_1991_);
                        v___x_2008_ = crate::leanh::lean_box(0);
                        v_isShared_2009_ = v_isSharedCheck_2016_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1998_ == 0 {
                    v___x_2000_ = v___x_1997_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1995_);
                    v___x_2000_ = v_reuseFailAlloc_2004_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
                    v___x_2002_ = v_reuseFailAlloc_2003_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2002_;
            }
            5 => {
                if v_isShared_2009_ == 0 {
                    v___x_2011_ = v___x_2008_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2006_);
                    v___x_2011_ = v_reuseFailAlloc_2015_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_2011_);
                    v___x_2013_ = v___x_1993_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2013_;
            }
            8 => {
                if v_isShared_2021_ == 0 {
                    v___x_2023_ = v___x_2020_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(
    mut v_f_2026_: *mut crate::leanh::LeanObject,
    mut v_s_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_b_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(v_f_2026_, v_s_2027_, v_a_2028_, v_b_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
    crate::leanh::lean_dec(v___y_2040_);
    crate::leanh::lean_dec_ref(v___y_2039_);
    crate::leanh::lean_dec(v___y_2038_);
    crate::leanh::lean_dec_ref(v___y_2037_);
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    crate::leanh::lean_dec(v___y_2034_);
    crate::leanh::lean_dec_ref(v___y_2033_);
    crate::leanh::lean_dec(v___y_2032_);
    crate::leanh::lean_dec(v___y_2031_);
    crate::leanh::lean_dec(v___y_2030_);
    return v_res_2042_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(
    mut v_f_2043_: *mut crate::leanh::LeanObject,
    mut v_keys_2044_: *mut crate::leanh::LeanObject,
    mut v_vals_2045_: *mut crate::leanh::LeanObject,
    mut v_i_2046_: *mut crate::leanh::LeanObject,
    mut v_acc_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_array_get_size(v_keys_2044_);
                v___x_2061_ = lean_nat_dec_lt(v_i_2046_, v___x_2060_);
                if v___x_2061_ == 0 {
                    crate::leanh::lean_dec(v_i_2046_);
                    crate::leanh::lean_dec_ref(v_f_2043_);
                    v___x_2062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2062_, 0, v_acc_2047_);
                    v___x_2063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2063_, 0, v___x_2062_);
                    return v___x_2063_;
                } else {
                    v_k_2064_ = lean_array_fget_borrowed(v_keys_2044_, v_i_2046_);
                    v_v_2065_ = lean_array_fget_borrowed(v_vals_2045_, v_i_2046_);
                    crate::leanh::lean_inc_ref(v_f_2043_);
                    crate::leanh::lean_inc(v___y_2058_);
                    crate::leanh::lean_inc_ref(v___y_2057_);
                    crate::leanh::lean_inc(v___y_2056_);
                    crate::leanh::lean_inc_ref(v___y_2055_);
                    crate::leanh::lean_inc(v___y_2054_);
                    crate::leanh::lean_inc_ref(v___y_2053_);
                    crate::leanh::lean_inc(v___y_2052_);
                    crate::leanh::lean_inc_ref(v___y_2051_);
                    crate::leanh::lean_inc(v___y_2050_);
                    crate::leanh::lean_inc(v___y_2049_);
                    crate::leanh::lean_inc(v___y_2048_);
                    crate::leanh::lean_inc(v_v_2065_);
                    crate::leanh::lean_inc(v_k_2064_);
                    v___x_2066_ = crate::leanh::lean_apply_15(
                        v_f_2043_,
                        v_acc_2047_,
                        v_k_2064_,
                        v_v_2065_,
                        v___y_2048_,
                        v___y_2049_,
                        v___y_2050_,
                        v___y_2051_,
                        v___y_2052_,
                        v___y_2053_,
                        v___y_2054_,
                        v___y_2055_,
                        v___y_2056_,
                        v___y_2057_,
                        v___y_2058_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2066_) == 0 {
                        v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                        crate::leanh::lean_inc(v_a_2067_);
                        if crate::leanh::lean_obj_tag(v_a_2067_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_2067_, 1);
                            crate::leanh::lean_dec(v_i_2046_);
                            crate::leanh::lean_dec_ref(v_f_2043_);
                            return v___x_2066_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2066_, 1);
                            v_a_2068_ = crate::leanh::lean_ctor_get(v_a_2067_, 0);
                            crate::leanh::lean_inc(v_a_2068_);
                            crate::leanh::lean_dec_ref_known(v_a_2067_, 1);
                            v___x_2069_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2070_ = lean_nat_add(v_i_2046_, v___x_2069_);
                            crate::leanh::lean_dec(v_i_2046_);
                            v_i_2046_ = v___x_2070_;
                            v_acc_2047_ = v_a_2068_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_2046_);
                        crate::leanh::lean_dec_ref(v_f_2043_);
                        return v___x_2066_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_2072_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_keys_2073_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_vals_2074_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_2075_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_acc_2076_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2077_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2078_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2079_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2080_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2081_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2082_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2083_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2084_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2085_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2086_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2087_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2088_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2072_, v_keys_2073_, v_vals_2074_, v_i_2075_, v_acc_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
    crate::leanh::lean_dec(v___y_2087_);
    crate::leanh::lean_dec_ref(v___y_2086_);
    crate::leanh::lean_dec(v___y_2085_);
    crate::leanh::lean_dec_ref(v___y_2084_);
    crate::leanh::lean_dec(v___y_2083_);
    crate::leanh::lean_dec_ref(v___y_2082_);
    crate::leanh::lean_dec(v___y_2081_);
    crate::leanh::lean_dec_ref(v___y_2080_);
    crate::leanh::lean_dec(v___y_2079_);
    crate::leanh::lean_dec(v___y_2078_);
    crate::leanh::lean_dec(v___y_2077_);
    crate::leanh::lean_dec_ref(v_vals_2074_);
    crate::leanh::lean_dec_ref(v_keys_2073_);
    return v_res_2089_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(
    mut v_f_2090_: *mut crate::leanh::LeanObject,
    mut v_x_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2108_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: usize = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: usize = 0;
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_ks_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2091_) == 0 {
                    v_es_2105_ = crate::leanh::lean_ctor_get(v_x_2091_, 0);
                    v_isSharedCheck_2127_ = (!crate::leanh::lean_is_exclusive(v_x_2091_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2107_ = v_x_2091_;
                        v_isShared_2108_ = v_isSharedCheck_2127_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_2105_);
                        crate::leanh::lean_dec(v_x_2091_);
                        v___x_2107_ = crate::leanh::lean_box(0);
                        v_isShared_2108_ = v_isSharedCheck_2127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_2128_ = crate::leanh::lean_ctor_get(v_x_2091_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2128_);
                    v_vs_2129_ = crate::leanh::lean_ctor_get(v_x_2091_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2129_);
                    crate::leanh::lean_dec_ref_known(v_x_2091_, 2);
                    v___x_2130_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2090_, v_ks_2128_, v_vs_2129_, v___x_2130_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                    crate::leanh::lean_dec_ref(v_vs_2129_);
                    crate::leanh::lean_dec_ref(v_ks_2128_);
                    return v___x_2131_;
                }
            }
            1 => {
                v___x_2109_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2110_ = lean_array_get_size(v_es_2105_);
                v___x_2111_ = lean_nat_dec_lt(v___x_2109_, v___x_2110_);
                if v___x_2111_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_2105_);
                    crate::leanh::lean_dec_ref(v_f_2090_);
                    if v_isShared_2108_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2107_, 1);
                        crate::leanh::lean_ctor_set(v___x_2107_, 0, v_x_2092_);
                        v___x_2113_ = v___x_2107_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_x_2092_);
                        v___x_2113_ = v_reuseFailAlloc_2115_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2116_ = lean_nat_dec_le(v___x_2110_, v___x_2110_);
                    if v___x_2116_ == 0 {
                        if v___x_2111_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_2105_);
                            crate::leanh::lean_dec_ref(v_f_2090_);
                            if v_isShared_2108_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2107_, 1);
                                crate::leanh::lean_ctor_set(v___x_2107_, 0, v_x_2092_);
                                v___x_2118_ = v___x_2107_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2120_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_x_2092_);
                                v___x_2118_ = v_reuseFailAlloc_2120_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2107_);
                            v___x_2121_ = 0usize;
                            v___x_2122_ = lean_usize_of_nat(v___x_2110_);
                            v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2090_, v_es_2105_, v___x_2121_, v___x_2122_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                            crate::leanh::lean_dec_ref(v_es_2105_);
                            return v___x_2123_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2107_);
                        v___x_2124_ = 0usize;
                        v___x_2125_ = lean_usize_of_nat(v___x_2110_);
                        v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2090_, v_es_2105_, v___x_2124_, v___x_2125_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                        crate::leanh::lean_dec_ref(v_es_2105_);
                        return v___x_2126_;
                    }
                }
            }
            2 => {
                v___x_2114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            3 => {
                v___x_2119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2118_);
                return v___x_2119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(
    mut v_f_2132_: *mut crate::leanh::LeanObject,
    mut v_as_2133_: *mut crate::leanh::LeanObject,
    mut v_i_2134_: usize,
    mut v_stop_2135_: usize,
    mut v_b_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___y_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2158_ = lean_usize_dec_eq(v_i_2134_, v_stop_2135_);
                if v___x_2158_ == 0 {
                    v___x_2159_ = lean_array_uget_borrowed(v_as_2133_, v_i_2134_);
                    match crate::leanh::lean_obj_tag(v___x_2159_) {
                        0 => {
                            v_key_2160_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                            v_val_2161_ = crate::leanh::lean_ctor_get(v___x_2159_, 1);
                            crate::leanh::lean_inc_ref(v_f_2132_);
                            crate::leanh::lean_inc(v___y_2147_);
                            crate::leanh::lean_inc_ref(v___y_2146_);
                            crate::leanh::lean_inc(v___y_2145_);
                            crate::leanh::lean_inc_ref(v___y_2144_);
                            crate::leanh::lean_inc(v___y_2143_);
                            crate::leanh::lean_inc_ref(v___y_2142_);
                            crate::leanh::lean_inc(v___y_2141_);
                            crate::leanh::lean_inc_ref(v___y_2140_);
                            crate::leanh::lean_inc(v___y_2139_);
                            crate::leanh::lean_inc(v___y_2138_);
                            crate::leanh::lean_inc(v___y_2137_);
                            crate::leanh::lean_inc(v_val_2161_);
                            crate::leanh::lean_inc(v_key_2160_);
                            v___x_2162_ = crate::leanh::lean_apply_15(
                                v_f_2132_,
                                v_b_2136_,
                                v_key_2160_,
                                v_val_2161_,
                                v___y_2137_,
                                v___y_2138_,
                                v___y_2139_,
                                v___y_2140_,
                                v___y_2141_,
                                v___y_2142_,
                                v___y_2143_,
                                v___y_2144_,
                                v___y_2145_,
                                v___y_2146_,
                                v___y_2147_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_2155_ = v___x_2162_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_2163_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                            crate::leanh::lean_inc(v_node_2163_);
                            crate::leanh::lean_inc_ref(v_f_2132_);
                            v___x_2164_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2132_, v_node_2163_, v_b_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
                            v___y_2155_ = v___x_2164_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_2150_ = v_b_2136_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2132_);
                    v___x_2165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2165_, 0, v_b_2136_);
                    v___x_2166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
                    return v___x_2166_;
                }
            }
            1 => {
                v___x_2151_ = 1usize;
                v___x_2152_ = lean_usize_add(v_i_2134_, v___x_2151_);
                v_i_2134_ = v___x_2152_;
                v_b_2136_ = v_a_2150_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2155_) == 0 {
                    v_a_2156_ = crate::leanh::lean_ctor_get(v___y_2155_, 0);
                    if crate::leanh::lean_obj_tag(v_a_2156_) == 0 {
                        crate::leanh::lean_dec_ref(v_f_2132_);
                        return v___y_2155_;
                    } else {
                        crate::leanh::lean_inc_ref(v_a_2156_);
                        crate::leanh::lean_dec_ref_known(v___y_2155_, 1);
                        v_a_2157_ = crate::leanh::lean_ctor_get(v_a_2156_, 0);
                        crate::leanh::lean_inc(v_a_2157_);
                        crate::leanh::lean_dec_ref_known(v_a_2156_, 1);
                        v_a_2150_ = v_a_2157_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2132_);
                    return v___y_2155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_2167_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_2168_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_i_2169_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_stop_2170_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_2171_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2172_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2173_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2174_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2175_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2176_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2177_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2178_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2179_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2180_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2181_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2182_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2183_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_i_boxed_2184_: usize = 0;
    let mut v_stop_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2184_ = crate::leanh::lean_unbox_usize(v_i_2169_);
    crate::leanh::lean_dec(v_i_2169_);
    v_stop_boxed_2185_ = crate::leanh::lean_unbox_usize(v_stop_2170_);
    crate::leanh::lean_dec(v_stop_2170_);
    v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2167_, v_as_2168_, v_i_boxed_2184_, v_stop_boxed_2185_, v_b_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
    crate::leanh::lean_dec(v___y_2182_);
    crate::leanh::lean_dec_ref(v___y_2181_);
    crate::leanh::lean_dec(v___y_2180_);
    crate::leanh::lean_dec_ref(v___y_2179_);
    crate::leanh::lean_dec(v___y_2178_);
    crate::leanh::lean_dec_ref(v___y_2177_);
    crate::leanh::lean_dec(v___y_2176_);
    crate::leanh::lean_dec_ref(v___y_2175_);
    crate::leanh::lean_dec(v___y_2174_);
    crate::leanh::lean_dec(v___y_2173_);
    crate::leanh::lean_dec(v___y_2172_);
    crate::leanh::lean_dec_ref(v_as_2168_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(
    mut v_f_2187_: *mut crate::leanh::LeanObject,
    mut v_x_2188_: *mut crate::leanh::LeanObject,
    mut v_x_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v___y_2198_: *mut crate::leanh::LeanObject,
    mut v___y_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2202_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2187_, v_x_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
    crate::leanh::lean_dec(v___y_2200_);
    crate::leanh::lean_dec_ref(v___y_2199_);
    crate::leanh::lean_dec(v___y_2198_);
    crate::leanh::lean_dec_ref(v___y_2197_);
    crate::leanh::lean_dec(v___y_2196_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    crate::leanh::lean_dec(v___y_2194_);
    crate::leanh::lean_dec_ref(v___y_2193_);
    crate::leanh::lean_dec(v___y_2192_);
    crate::leanh::lean_dec(v___y_2191_);
    crate::leanh::lean_dec(v___y_2190_);
    return v_res_2202_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(
    mut v_map_2203_: *mut crate::leanh::LeanObject,
    mut v_init_2204_: *mut crate::leanh::LeanObject,
    mut v_f_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v_a_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_a_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2218_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                crate::leanh::lean_closure_set(v___f_2218_, 0, v_f_2205_);
                crate::leanh::lean_inc_ref(v_map_2203_);
                v___x_2219_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v___f_2218_, v_map_2203_, v_init_2204_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
                if crate::leanh::lean_obj_tag(v___x_2219_) == 0 {
                    v_a_2220_ = crate::leanh::lean_ctor_get(v___x_2219_, 0);
                    v_isSharedCheck_2228_ = (!crate::leanh::lean_is_exclusive(v___x_2219_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v___x_2222_ = v___x_2219_;
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2220_);
                        crate::leanh::lean_dec(v___x_2219_);
                        v___x_2222_ = crate::leanh::lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2229_ = crate::leanh::lean_ctor_get(v___x_2219_, 0);
                    v_isSharedCheck_2236_ = (!crate::leanh::lean_is_exclusive(v___x_2219_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v___x_2219_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2229_);
                        crate::leanh::lean_dec(v___x_2219_);
                        v___x_2231_ = crate::leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2224_ = crate::leanh::lean_ctor_get(v_a_2220_, 0);
                crate::leanh::lean_inc(v_a_2224_);
                crate::leanh::lean_dec(v_a_2220_);
                if v_isShared_2223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2222_, 0, v_a_2224_);
                    v___x_2226_ = v___x_2222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2224_);
                    v___x_2226_ = v_reuseFailAlloc_2227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2226_;
            }
            3 => {
                if v_isShared_2232_ == 0 {
                    v___x_2234_ = v___x_2231_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2235_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___boxed(
    mut v_map_2237_: *mut crate::leanh::LeanObject,
    mut v_init_2238_: *mut crate::leanh::LeanObject,
    mut v_f_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_2237_, v_init_2238_, v_f_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec_ref(v___y_2249_);
    crate::leanh::lean_dec(v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2247_);
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    crate::leanh::lean_dec(v___y_2244_);
    crate::leanh::lean_dec_ref(v___y_2243_);
    crate::leanh::lean_dec(v___y_2242_);
    crate::leanh::lean_dec(v___y_2241_);
    crate::leanh::lean_dec(v___y_2240_);
    crate::leanh::lean_dec_ref(v_map_2237_);
    return v_res_2252_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0;
    v___x_2255_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2256_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_2257_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1;
    v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_2259_ = l_mkPanicMessageWithDecl(
        v___x_2258_,
        v___x_2257_,
        v___x_2256_,
        v___x_2255_,
        v___x_2254_,
    );
    return v___x_2259_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(
    mut v_a_2260_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v_size_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2291_: u8 = 0;
    let mut v_a_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_a_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2272_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_,
                    v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_,
                );
                if crate::leanh::lean_obj_tag(v___x_2272_) == 0 {
                    v_a_2273_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                    crate::leanh::lean_inc(v_a_2273_);
                    crate::leanh::lean_dec_ref_known(v___x_2272_, 1);
                    v_vars_2274_ = crate::leanh::lean_ctor_get(v_a_2273_, 10);
                    crate::leanh::lean_inc_ref_n(v_vars_2274_, 2);
                    v_varMap_2275_ = crate::leanh::lean_ctor_get(v_a_2273_, 11);
                    crate::leanh::lean_inc_ref(v_varMap_2275_);
                    crate::leanh::lean_dec(v_a_2273_);
                    v___f_2276_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    crate::leanh::lean_closure_set(v___f_2276_, 0, v_vars_2274_);
                    v___x_2277_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2278_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_varMap_2275_, v___x_2277_, v___f_2276_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
                    crate::leanh::lean_dec_ref(v_varMap_2275_);
                    if crate::leanh::lean_obj_tag(v___x_2278_) == 0 {
                        v_a_2279_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2291_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2291_ == 0 {
                            v___x_2281_ = v___x_2278_;
                            v_isShared_2282_ = v_isSharedCheck_2291_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2279_);
                            crate::leanh::lean_dec(v___x_2278_);
                            v___x_2281_ = crate::leanh::lean_box(0);
                            v_isShared_2282_ = v_isSharedCheck_2291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_vars_2274_);
                        v_a_2292_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2299_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v___x_2294_ = v___x_2278_;
                            v_isShared_2295_ = v_isSharedCheck_2299_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2292_);
                            crate::leanh::lean_dec(v___x_2278_);
                            v___x_2294_ = crate::leanh::lean_box(0);
                            v_isShared_2295_ = v_isSharedCheck_2299_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2300_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                    v_isSharedCheck_2307_ = (!crate::leanh::lean_is_exclusive(v___x_2272_)) as u8;
                    if v_isSharedCheck_2307_ == 0 {
                        v___x_2302_ = v___x_2272_;
                        v_isShared_2303_ = v_isSharedCheck_2307_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2300_);
                        crate::leanh::lean_dec(v___x_2272_);
                        v___x_2302_ = crate::leanh::lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2307_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_2283_ = crate::leanh::lean_ctor_get(v_vars_2274_, 2);
                crate::leanh::lean_inc(v_size_2283_);
                crate::leanh::lean_dec_ref(v_vars_2274_);
                v___x_2284_ = lean_nat_dec_eq(v_size_2283_, v_a_2279_);
                crate::leanh::lean_dec(v_a_2279_);
                crate::leanh::lean_dec(v_size_2283_);
                if v___x_2284_ == 0 {
                    crate::leanh::lean_del_object(v___x_2281_);
                    v___x_2285_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1);
                    v___x_2286_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2285_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
                    return v___x_2286_;
                } else {
                    v___x_2287_ = crate::leanh::lean_box(0);
                    if v_isShared_2282_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2281_, 0, v___x_2287_);
                        v___x_2289_ = v___x_2281_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
                        v___x_2289_ = v_reuseFailAlloc_2290_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2289_;
            }
            3 => {
                if v_isShared_2295_ == 0 {
                    v___x_2297_ = v___x_2294_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2297_;
            }
            5 => {
                if v_isShared_2303_ == 0 {
                    v___x_2305_ = v___x_2302_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
                    v___x_2305_ = v_reuseFailAlloc_2306_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___boxed(
    mut v_a_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
    mut v_a_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_a_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(
        v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_,
        v_a_2316_, v_a_2317_, v_a_2318_,
    );
    crate::leanh::lean_dec(v_a_2318_);
    crate::leanh::lean_dec_ref(v_a_2317_);
    crate::leanh::lean_dec(v_a_2316_);
    crate::leanh::lean_dec_ref(v_a_2315_);
    crate::leanh::lean_dec(v_a_2314_);
    crate::leanh::lean_dec_ref(v_a_2313_);
    crate::leanh::lean_dec(v_a_2312_);
    crate::leanh::lean_dec_ref(v_a_2311_);
    crate::leanh::lean_dec(v_a_2310_);
    crate::leanh::lean_dec(v_a_2309_);
    crate::leanh::lean_dec(v_a_2308_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(
    mut v_00_u03c3_2321_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2322_: *mut crate::leanh::LeanObject,
    mut v_map_2323_: *mut crate::leanh::LeanObject,
    mut v_init_2324_: *mut crate::leanh::LeanObject,
    mut v_f_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_2323_, v_init_2324_, v_f_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_2339_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_2340_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_map_2341_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_init_2342_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_2343_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2344_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2345_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2346_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2347_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2348_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2349_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2350_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2351_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2352_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2353_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2354_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2355_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(v_00_u03c3_2339_, v_00_u03b2_2340_, v_map_2341_, v_init_2342_, v_f_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    crate::leanh::lean_dec(v___y_2352_);
    crate::leanh::lean_dec_ref(v___y_2351_);
    crate::leanh::lean_dec(v___y_2350_);
    crate::leanh::lean_dec_ref(v___y_2349_);
    crate::leanh::lean_dec(v___y_2348_);
    crate::leanh::lean_dec_ref(v___y_2347_);
    crate::leanh::lean_dec(v___y_2346_);
    crate::leanh::lean_dec(v___y_2345_);
    crate::leanh::lean_dec(v___y_2344_);
    crate::leanh::lean_dec_ref(v_map_2341_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(
    mut v_map_2357_: *mut crate::leanh::LeanObject,
    mut v_f_2358_: *mut crate::leanh::LeanObject,
    mut v_init_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2358_, v_map_2357_, v_init_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
    return v___x_2372_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(
    mut v_map_2373_: *mut crate::leanh::LeanObject,
    mut v_f_2374_: *mut crate::leanh::LeanObject,
    mut v_init_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2388_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(v_map_2373_, v_f_2374_, v_init_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
    crate::leanh::lean_dec(v___y_2386_);
    crate::leanh::lean_dec_ref(v___y_2385_);
    crate::leanh::lean_dec(v___y_2384_);
    crate::leanh::lean_dec_ref(v___y_2383_);
    crate::leanh::lean_dec(v___y_2382_);
    crate::leanh::lean_dec_ref(v___y_2381_);
    crate::leanh::lean_dec(v___y_2380_);
    crate::leanh::lean_dec_ref(v___y_2379_);
    crate::leanh::lean_dec(v___y_2378_);
    crate::leanh::lean_dec(v___y_2377_);
    crate::leanh::lean_dec(v___y_2376_);
    return v_res_2388_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(
    mut v_00_u03c3_2389_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2390_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2391_: *mut crate::leanh::LeanObject,
    mut v_map_2392_: *mut crate::leanh::LeanObject,
    mut v_f_2393_: *mut crate::leanh::LeanObject,
    mut v_init_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2407_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2393_, v_map_2392_, v_init_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    return v___x_2407_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_2408_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_2409_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b2_2410_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_map_2411_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_2412_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_init_2413_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2414_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2415_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2416_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2417_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2418_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2419_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2420_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2421_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2422_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2423_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2424_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2425_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2426_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(v_00_u03c3_2408_, v_00_u03c3_2409_, v_00_u03b2_2410_, v_map_2411_, v_f_2412_, v_init_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
    crate::leanh::lean_dec(v___y_2424_);
    crate::leanh::lean_dec_ref(v___y_2423_);
    crate::leanh::lean_dec(v___y_2422_);
    crate::leanh::lean_dec_ref(v___y_2421_);
    crate::leanh::lean_dec(v___y_2420_);
    crate::leanh::lean_dec_ref(v___y_2419_);
    crate::leanh::lean_dec(v___y_2418_);
    crate::leanh::lean_dec_ref(v___y_2417_);
    crate::leanh::lean_dec(v___y_2416_);
    crate::leanh::lean_dec(v___y_2415_);
    crate::leanh::lean_dec(v___y_2414_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(
    mut v_00_u03c3_2427_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2428_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2430_: *mut crate::leanh::LeanObject,
    mut v_f_2431_: *mut crate::leanh::LeanObject,
    mut v_x_2432_: *mut crate::leanh::LeanObject,
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2431_, v_x_2432_, v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
    return v___x_2446_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_2447_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_2448_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_2449_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_2450_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_2451_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_x_2452_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_x_2453_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2454_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2455_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2456_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2457_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2458_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2459_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2460_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2461_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2462_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2463_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2464_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2465_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_2447_, v_00_u03c3_2448_, v_00_u03b1_2449_, v_00_u03b2_2450_, v_f_2451_, v_x_2452_, v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
    crate::leanh::lean_dec(v___y_2464_);
    crate::leanh::lean_dec_ref(v___y_2463_);
    crate::leanh::lean_dec(v___y_2462_);
    crate::leanh::lean_dec_ref(v___y_2461_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2459_);
    crate::leanh::lean_dec(v___y_2458_);
    crate::leanh::lean_dec_ref(v___y_2457_);
    crate::leanh::lean_dec(v___y_2456_);
    crate::leanh::lean_dec(v___y_2455_);
    crate::leanh::lean_dec(v___y_2454_);
    return v_res_2466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(
    mut v_00_u03b1_2467_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2468_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2469_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2470_: *mut crate::leanh::LeanObject,
    mut v_f_2471_: *mut crate::leanh::LeanObject,
    mut v_as_2472_: *mut crate::leanh::LeanObject,
    mut v_i_2473_: usize,
    mut v_stop_2474_: usize,
    mut v_b_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
    mut v___y_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2471_, v_as_2472_, v_i_2473_, v_stop_2474_, v_b_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
    return v___x_2488_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_2489_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_2490_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3_2491_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3_2492_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_2493_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_as_2494_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_i_2495_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_stop_2496_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_2497_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2498_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2499_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2500_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2501_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2502_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2503_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2504_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2505_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2506_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2507_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2508_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2509_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_i_boxed_2510_: usize = 0;
    let mut v_stop_boxed_2511_: usize = 0;
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2510_ = crate::leanh::lean_unbox_usize(v_i_2495_);
    crate::leanh::lean_dec(v_i_2495_);
    v_stop_boxed_2511_ = crate::leanh::lean_unbox_usize(v_stop_2496_);
    crate::leanh::lean_dec(v_stop_2496_);
    v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_2489_, v_00_u03b2_2490_, v_00_u03c3_2491_, v_00_u03c3_2492_, v_f_2493_, v_as_2494_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
    crate::leanh::lean_dec(v___y_2508_);
    crate::leanh::lean_dec_ref(v___y_2507_);
    crate::leanh::lean_dec(v___y_2506_);
    crate::leanh::lean_dec_ref(v___y_2505_);
    crate::leanh::lean_dec(v___y_2504_);
    crate::leanh::lean_dec_ref(v___y_2503_);
    crate::leanh::lean_dec(v___y_2502_);
    crate::leanh::lean_dec_ref(v___y_2501_);
    crate::leanh::lean_dec(v___y_2500_);
    crate::leanh::lean_dec(v___y_2499_);
    crate::leanh::lean_dec(v___y_2498_);
    crate::leanh::lean_dec_ref(v_as_2494_);
    return v_res_2512_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(
    mut v_00_u03c3_2513_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2516_: *mut crate::leanh::LeanObject,
    mut v_f_2517_: *mut crate::leanh::LeanObject,
    mut v_keys_2518_: *mut crate::leanh::LeanObject,
    mut v_vals_2519_: *mut crate::leanh::LeanObject,
    mut v_heq_2520_: *mut crate::leanh::LeanObject,
    mut v_i_2521_: *mut crate::leanh::LeanObject,
    mut v_acc_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2517_, v_keys_2518_, v_vals_2519_, v_i_2521_, v_acc_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
    return v___x_2535_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_2536_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_2537_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_2538_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_2539_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_2540_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_keys_2541_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_vals_2542_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_heq_2543_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_i_2544_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_acc_2545_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2546_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2547_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2548_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2549_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2550_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2551_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2552_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2553_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2554_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2555_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2556_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_2557_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_res_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_2536_, v_00_u03c3_2537_, v_00_u03b1_2538_, v_00_u03b2_2539_, v_f_2540_, v_keys_2541_, v_vals_2542_, v_heq_2543_, v_i_2544_, v_acc_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
    crate::leanh::lean_dec(v___y_2556_);
    crate::leanh::lean_dec_ref(v___y_2555_);
    crate::leanh::lean_dec(v___y_2554_);
    crate::leanh::lean_dec_ref(v___y_2553_);
    crate::leanh::lean_dec(v___y_2552_);
    crate::leanh::lean_dec_ref(v___y_2551_);
    crate::leanh::lean_dec(v___y_2550_);
    crate::leanh::lean_dec_ref(v___y_2549_);
    crate::leanh::lean_dec(v___y_2548_);
    crate::leanh::lean_dec(v___y_2547_);
    crate::leanh::lean_dec(v___y_2546_);
    crate::leanh::lean_dec_ref(v_vals_2542_);
    crate::leanh::lean_dec_ref(v_keys_2541_);
    return v_res_2558_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2561_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1;
    v___x_2562_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_2563_ = crate::leanh::lean_unsigned_to_nat(36);
    v___x_2564_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0;
    v___x_2565_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_2566_ = l_mkPanicMessageWithDecl(
        v___x_2565_,
        v___x_2564_,
        v___x_2563_,
        v___x_2562_,
        v___x_2561_,
    );
    return v___x_2566_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4;
    v___x_2571_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_2572_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_2573_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0;
    v___x_2574_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_2575_ = l_mkPanicMessageWithDecl(
        v___x_2574_,
        v___x_2573_,
        v___x_2572_,
        v___x_2571_,
        v___x_2570_,
    );
    return v___x_2575_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6;
    v___x_2578_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2579_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_2580_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0;
    v___x_2581_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_2582_ = l_mkPanicMessageWithDecl(
        v___x_2581_,
        v___x_2580_,
        v___x_2579_,
        v___x_2578_,
        v___x_2577_,
    );
    return v___x_2582_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(
    mut v_s_2583_: *mut crate::leanh::LeanObject,
    mut v_simplified_2584_: u8,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_a_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v_a_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___y_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: u8 = 0;
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2677_: u8 = 0;
    let mut v_a_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2635_ = l_Lean_Meta_Grind_AC_isCommutative(
                    v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_,
                    v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_,
                );
                if crate::leanh::lean_obj_tag(v___x_2635_) == 0 {
                    v_a_2636_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2677_ = (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2677_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2677_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2636_);
                        crate::leanh::lean_dec(v___x_2635_);
                        v___x_2638_ = crate::leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2677_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2678_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2685_ = (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v___x_2680_ = v___x_2635_;
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2678_);
                        crate::leanh::lean_dec(v___x_2635_);
                        v___x_2680_ = crate::leanh::lean_box(0);
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2609_ = l_Lean_Meta_Grind_AC_isIdempotent(
                    v___y_2598_,
                    v___y_2599_,
                    v___y_2600_,
                    v___y_2601_,
                    v___y_2602_,
                    v___y_2603_,
                    v___y_2604_,
                    v___y_2605_,
                    v___y_2606_,
                    v___y_2607_,
                    v___y_2608_,
                );
                if crate::leanh::lean_obj_tag(v___x_2609_) == 0 {
                    v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2626_ = (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2612_ = v___x_2609_;
                        v_isShared_2613_ = v_isSharedCheck_2626_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2610_);
                        crate::leanh::lean_dec(v___x_2609_);
                        v___x_2612_ = crate::leanh::lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2626_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2627_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2634_ = (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2609_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2627_);
                        crate::leanh::lean_dec(v___x_2609_);
                        v___x_2629_ = crate::leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2614_ = (crate::leanh::lean_unbox(v_a_2610_) as u8);
                crate::leanh::lean_dec(v_a_2610_);
                if v___x_2614_ == 0 {
                    v___x_2615_ = crate::leanh::lean_box(0);
                    if v_isShared_2613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2615_);
                        v___x_2617_ = v___x_2612_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
                        v___x_2617_ = v_reuseFailAlloc_2618_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2619_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_2583_);
                    if v___x_2619_ == 0 {
                        crate::leanh::lean_del_object(v___x_2612_);
                        v___x_2620_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2);
                        v___x_2621_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2620_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
                        return v___x_2621_;
                    } else {
                        v___x_2622_ = crate::leanh::lean_box(0);
                        if v_isShared_2613_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2622_);
                            v___x_2624_ = v___x_2612_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2625_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
                            v___x_2624_ = v_reuseFailAlloc_2625_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_2617_;
            }
            4 => {
                return v___x_2624_;
            }
            5 => {
                if v_isShared_2630_ == 0 {
                    v___x_2632_ = v___x_2629_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2632_;
            }
            7 => {
                v___x_2673_ = (crate::leanh::lean_unbox(v_a_2636_) as u8);
                crate::leanh::lean_dec(v_a_2636_);
                if v___x_2673_ == 0 {
                    v___y_2641_ = v_a_2585_;
                    v___y_2642_ = v_a_2586_;
                    v___y_2643_ = v_a_2587_;
                    v___y_2644_ = v_a_2588_;
                    v___y_2645_ = v_a_2589_;
                    v___y_2646_ = v_a_2590_;
                    v___y_2647_ = v_a_2591_;
                    v___y_2648_ = v_a_2592_;
                    v___y_2649_ = v_a_2593_;
                    v___y_2650_ = v_a_2594_;
                    v___y_2651_ = v_a_2595_;
                    state = 8;
                    continue;
                } else {
                    v___x_2674_ = l_Lean_Grind_AC_Seq_isSorted(v_s_2583_);
                    if v___x_2674_ == 0 {
                        crate::leanh::lean_del_object(v___x_2638_);
                        v___x_2675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7);
                        v___x_2676_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2675_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
                        return v___x_2676_;
                    } else {
                        v___y_2641_ = v_a_2585_;
                        v___y_2642_ = v_a_2586_;
                        v___y_2643_ = v_a_2587_;
                        v___y_2644_ = v_a_2588_;
                        v___y_2645_ = v_a_2589_;
                        v___y_2646_ = v_a_2590_;
                        v___y_2647_ = v_a_2591_;
                        v___y_2648_ = v_a_2592_;
                        v___y_2649_ = v_a_2593_;
                        v___y_2650_ = v_a_2594_;
                        v___y_2651_ = v_a_2595_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_simplified_2584_ == 0 {
                    v___x_2652_ = crate::leanh::lean_box(0);
                    if v_isShared_2639_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2652_);
                        v___x_2654_ = v___x_2638_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
                        v___x_2654_ = v_reuseFailAlloc_2655_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2638_);
                    v___x_2656_ = l_Lean_Meta_Grind_AC_hasNeutral(
                        v___y_2641_,
                        v___y_2642_,
                        v___y_2643_,
                        v___y_2644_,
                        v___y_2645_,
                        v___y_2646_,
                        v___y_2647_,
                        v___y_2648_,
                        v___y_2649_,
                        v___y_2650_,
                        v___y_2651_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                        v_a_2657_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                        crate::leanh::lean_inc(v_a_2657_);
                        crate::leanh::lean_dec_ref_known(v___x_2656_, 1);
                        v___x_2658_ = (crate::leanh::lean_unbox(v_a_2657_) as u8);
                        crate::leanh::lean_dec(v_a_2657_);
                        if v___x_2658_ == 0 {
                            v___y_2598_ = v___y_2641_;
                            v___y_2599_ = v___y_2642_;
                            v___y_2600_ = v___y_2643_;
                            v___y_2601_ = v___y_2644_;
                            v___y_2602_ = v___y_2645_;
                            v___y_2603_ = v___y_2646_;
                            v___y_2604_ = v___y_2647_;
                            v___y_2605_ = v___y_2648_;
                            v___y_2606_ = v___y_2649_;
                            v___y_2607_ = v___y_2650_;
                            v___y_2608_ = v___y_2651_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2659_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2660_ = l_Lean_Grind_AC_Seq_contains(v_s_2583_, v___x_2659_);
                            if v___x_2660_ == 0 {
                                v___y_2598_ = v___y_2641_;
                                v___y_2599_ = v___y_2642_;
                                v___y_2600_ = v___y_2643_;
                                v___y_2601_ = v___y_2644_;
                                v___y_2602_ = v___y_2645_;
                                v___y_2603_ = v___y_2646_;
                                v___y_2604_ = v___y_2647_;
                                v___y_2605_ = v___y_2648_;
                                v___y_2606_ = v___y_2649_;
                                v___y_2607_ = v___y_2650_;
                                v___y_2608_ = v___y_2651_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2661_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3;
                                v___x_2662_ =
                                    l_Lean_Grind_AC_instBEqSeq_beq(v_s_2583_, v___x_2661_);
                                if v___x_2662_ == 0 {
                                    v___x_2663_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5);
                                    v___x_2664_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2663_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
                                    return v___x_2664_;
                                } else {
                                    v___y_2598_ = v___y_2641_;
                                    v___y_2599_ = v___y_2642_;
                                    v___y_2600_ = v___y_2643_;
                                    v___y_2601_ = v___y_2644_;
                                    v___y_2602_ = v___y_2645_;
                                    v___y_2603_ = v___y_2646_;
                                    v___y_2604_ = v___y_2647_;
                                    v___y_2605_ = v___y_2648_;
                                    v___y_2606_ = v___y_2649_;
                                    v___y_2607_ = v___y_2650_;
                                    v___y_2608_ = v___y_2651_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_2665_ = crate::leanh::lean_ctor_get(v___x_2656_, 0);
                        v_isSharedCheck_2672_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2656_)) as u8;
                        if v_isSharedCheck_2672_ == 0 {
                            v___x_2667_ = v___x_2656_;
                            v_isShared_2668_ = v_isSharedCheck_2672_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2665_);
                            crate::leanh::lean_dec(v___x_2656_);
                            v___x_2667_ = crate::leanh::lean_box(0);
                            v_isShared_2668_ = v_isSharedCheck_2672_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_2654_;
            }
            10 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2670_;
            }
            12 => {
                if v_isShared_2681_ == 0 {
                    v___x_2683_ = v___x_2680_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
                    v___x_2683_ = v_reuseFailAlloc_2684_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(
    mut v_s_2686_: *mut crate::leanh::LeanObject,
    mut v_simplified_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
    mut v_a_2691_: *mut crate::leanh::LeanObject,
    mut v_a_2692_: *mut crate::leanh::LeanObject,
    mut v_a_2693_: *mut crate::leanh::LeanObject,
    mut v_a_2694_: *mut crate::leanh::LeanObject,
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simplified_boxed_2700_: u8 = 0;
    let mut v_res_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simplified_boxed_2700_ = (crate::leanh::lean_unbox(v_simplified_2687_) as u8);
    v_res_2701_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(
        v_s_2686_,
        v_simplified_boxed_2700_,
        v_a_2688_,
        v_a_2689_,
        v_a_2690_,
        v_a_2691_,
        v_a_2692_,
        v_a_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
    );
    crate::leanh::lean_dec(v_a_2698_);
    crate::leanh::lean_dec_ref(v_a_2697_);
    crate::leanh::lean_dec(v_a_2696_);
    crate::leanh::lean_dec_ref(v_a_2695_);
    crate::leanh::lean_dec(v_a_2694_);
    crate::leanh::lean_dec_ref(v_a_2693_);
    crate::leanh::lean_dec(v_a_2692_);
    crate::leanh::lean_dec_ref(v_a_2691_);
    crate::leanh::lean_dec(v_a_2690_);
    crate::leanh::lean_dec(v_a_2689_);
    crate::leanh::lean_dec(v_a_2688_);
    crate::leanh::lean_dec_ref(v_s_2686_);
    return v_res_2701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
    mut v_lhs_2702_: *mut crate::leanh::LeanObject,
    mut v_rhs_2703_: *mut crate::leanh::LeanObject,
    mut v_simplified_2704_: u8,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2717_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(
        v_lhs_2702_,
        v_simplified_2704_,
        v_a_2705_,
        v_a_2706_,
        v_a_2707_,
        v_a_2708_,
        v_a_2709_,
        v_a_2710_,
        v_a_2711_,
        v_a_2712_,
        v_a_2713_,
        v_a_2714_,
        v_a_2715_,
    );
    if crate::leanh::lean_obj_tag(v___x_2717_) == 0 {
        let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2717_, 1);
        v___x_2718_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(
            v_rhs_2703_,
            v_simplified_2704_,
            v_a_2705_,
            v_a_2706_,
            v_a_2707_,
            v_a_2708_,
            v_a_2709_,
            v_a_2710_,
            v_a_2711_,
            v_a_2712_,
            v_a_2713_,
            v_a_2714_,
            v_a_2715_,
        );
        return v___x_2718_;
    } else {
        return v___x_2717_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(
    mut v_lhs_2719_: *mut crate::leanh::LeanObject,
    mut v_rhs_2720_: *mut crate::leanh::LeanObject,
    mut v_simplified_2721_: *mut crate::leanh::LeanObject,
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
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simplified_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simplified_boxed_2734_ = (crate::leanh::lean_unbox(v_simplified_2721_) as u8);
    v_res_2735_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
        v_lhs_2719_,
        v_rhs_2720_,
        v_simplified_boxed_2734_,
        v_a_2722_,
        v_a_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
    );
    crate::leanh::lean_dec(v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    crate::leanh::lean_dec(v_a_2726_);
    crate::leanh::lean_dec_ref(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec(v_a_2723_);
    crate::leanh::lean_dec(v_a_2722_);
    crate::leanh::lean_dec_ref(v_rhs_2720_);
    crate::leanh::lean_dec_ref(v_lhs_2719_);
    return v_res_2735_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_2736_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(
    mut v_msg_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
    mut v___y_2744_: *mut crate::leanh::LeanObject,
    mut v___y_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765__overap_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0);
    v___f_2751_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2751_, 0, v___x_2750_);
    v___x_3765__overap_2752_ = lean_panic_fn_borrowed(v___f_2751_, v_msg_2737_);
    crate::leanh::lean_dec_ref(v___f_2751_);
    crate::leanh::lean_inc(v___y_2748_);
    crate::leanh::lean_inc_ref(v___y_2747_);
    crate::leanh::lean_inc(v___y_2746_);
    crate::leanh::lean_inc_ref(v___y_2745_);
    crate::leanh::lean_inc(v___y_2744_);
    crate::leanh::lean_inc_ref(v___y_2743_);
    crate::leanh::lean_inc(v___y_2742_);
    crate::leanh::lean_inc_ref(v___y_2741_);
    crate::leanh::lean_inc(v___y_2740_);
    crate::leanh::lean_inc(v___y_2739_);
    crate::leanh::lean_inc(v___y_2738_);
    v___x_2753_ = crate::leanh::lean_apply_12(
        v___x_3765__overap_2752_,
        v___y_2738_,
        v___y_2739_,
        v___y_2740_,
        v___y_2741_,
        v___y_2742_,
        v___y_2743_,
        v___y_2744_,
        v___y_2745_,
        v___y_2746_,
        v___y_2747_,
        v___y_2748_,
        crate::leanh::lean_box(0),
    );
    return v___x_2753_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(
    mut v_msg_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
    crate::leanh::lean_dec(v___y_2765_);
    crate::leanh::lean_dec_ref(v___y_2764_);
    crate::leanh::lean_dec(v___y_2763_);
    crate::leanh::lean_dec_ref(v___y_2762_);
    crate::leanh::lean_dec(v___y_2761_);
    crate::leanh::lean_dec_ref(v___y_2760_);
    crate::leanh::lean_dec(v___y_2759_);
    crate::leanh::lean_dec_ref(v___y_2758_);
    crate::leanh::lean_dec(v___y_2757_);
    crate::leanh::lean_dec(v___y_2756_);
    crate::leanh::lean_dec(v___y_2755_);
    return v_res_2767_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1;
    v___x_2771_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2772_ = crate::leanh::lean_unsigned_to_nat(43);
    v___x_2773_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0;
    v___x_2774_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0;
    v___x_2775_ = l_mkPanicMessageWithDecl(
        v___x_2774_,
        v___x_2773_,
        v___x_2772_,
        v___x_2771_,
        v___x_2770_,
    );
    return v___x_2775_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(
    mut v_as_x27_2776_: *mut crate::leanh::LeanObject,
    mut v_b_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
    mut v___y_2780_: *mut crate::leanh::LeanObject,
    mut v___y_2781_: *mut crate::leanh::LeanObject,
    mut v___y_2782_: *mut crate::leanh::LeanObject,
    mut v___y_2783_: *mut crate::leanh::LeanObject,
    mut v___y_2784_: *mut crate::leanh::LeanObject,
    mut v___y_2785_: *mut crate::leanh::LeanObject,
    mut v___y_2786_: *mut crate::leanh::LeanObject,
    mut v___y_2787_: *mut crate::leanh::LeanObject,
    mut v___y_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v_a_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2776_) == 0 {
                    v___x_2790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2790_, 0, v_b_2777_);
                    return v___x_2790_;
                } else {
                    v_head_2791_ = crate::leanh::lean_ctor_get(v_as_x27_2776_, 0);
                    v_tail_2792_ = crate::leanh::lean_ctor_get(v_as_x27_2776_, 1);
                    v_lhs_2793_ = crate::leanh::lean_ctor_get(v_head_2791_, 0);
                    v_rhs_2794_ = crate::leanh::lean_ctor_get(v_head_2791_, 1);
                    v___x_2795_ = l_Lean_Grind_AC_Seq_compare(v_lhs_2793_, v_rhs_2794_);
                    v___x_2796_ = 2;
                    v___x_2797_ = l_instDecidableEqOrdering(v___x_2795_, v___x_2796_);
                    if v___x_2797_ == 0 {
                        v___x_2798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2);
                        v___x_2799_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v___x_2798_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
                        if crate::leanh::lean_obj_tag(v___x_2799_) == 0 {
                            v_a_2800_ = crate::leanh::lean_ctor_get(v___x_2799_, 0);
                            v_isSharedCheck_2810_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2799_)) as u8;
                            if v_isSharedCheck_2810_ == 0 {
                                v___x_2802_ = v___x_2799_;
                                v_isShared_2803_ = v_isSharedCheck_2810_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2800_);
                                crate::leanh::lean_dec(v___x_2799_);
                                v___x_2802_ = crate::leanh::lean_box(0);
                                v_isShared_2803_ = v_isSharedCheck_2810_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2811_ = crate::leanh::lean_ctor_get(v___x_2799_, 0);
                            v_isSharedCheck_2818_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2799_)) as u8;
                            if v_isSharedCheck_2818_ == 0 {
                                v___x_2813_ = v___x_2799_;
                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2811_);
                                crate::leanh::lean_dec(v___x_2799_);
                                v___x_2813_ = crate::leanh::lean_box(0);
                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2819_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_2793_, v_rhs_2794_, v___x_2797_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
                        if crate::leanh::lean_obj_tag(v___x_2819_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2819_, 1);
                            v___x_2820_ = crate::leanh::lean_box(0);
                            v_as_x27_2776_ = v_tail_2792_;
                            v_b_2777_ = v___x_2820_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2819_;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2800_) == 0 {
                    v_a_2804_ = crate::leanh::lean_ctor_get(v_a_2800_, 0);
                    crate::leanh::lean_inc(v_a_2804_);
                    crate::leanh::lean_dec_ref_known(v_a_2800_, 1);
                    if v_isShared_2803_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2802_, 0, v_a_2804_);
                        v___x_2806_ = v___x_2802_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2804_);
                        v___x_2806_ = v_reuseFailAlloc_2807_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2802_);
                    v_a_2808_ = crate::leanh::lean_ctor_get(v_a_2800_, 0);
                    crate::leanh::lean_inc(v_a_2808_);
                    crate::leanh::lean_dec_ref_known(v_a_2800_, 1);
                    v_as_x27_2776_ = v_tail_2792_;
                    v_b_2777_ = v_a_2808_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_2806_;
            }
            3 => {
                if v_isShared_2814_ == 0 {
                    v___x_2816_ = v___x_2813_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___boxed(
    mut v_as_x27_2822_: *mut crate::leanh::LeanObject,
    mut v_b_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_2822_, v_b_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
    crate::leanh::lean_dec(v___y_2834_);
    crate::leanh::lean_dec_ref(v___y_2833_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    crate::leanh::lean_dec(v___y_2830_);
    crate::leanh::lean_dec_ref(v___y_2829_);
    crate::leanh::lean_dec(v___y_2828_);
    crate::leanh::lean_dec_ref(v___y_2827_);
    crate::leanh::lean_dec(v___y_2826_);
    crate::leanh::lean_dec(v___y_2825_);
    crate::leanh::lean_dec(v___y_2824_);
    crate::leanh::lean_dec(v_as_x27_2822_);
    return v_res_2836_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
    mut v_a_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_unused_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2849_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_,
                    v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_,
                );
                if crate::leanh::lean_obj_tag(v___x_2849_) == 0 {
                    v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2849_, 0);
                    crate::leanh::lean_inc(v_a_2850_);
                    crate::leanh::lean_dec_ref_known(v___x_2849_, 1);
                    v_basis_2851_ = crate::leanh::lean_ctor_get(v_a_2850_, 15);
                    crate::leanh::lean_inc(v_basis_2851_);
                    crate::leanh::lean_dec(v_a_2850_);
                    v___x_2852_ = crate::leanh::lean_box(0);
                    v___x_2853_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_basis_2851_, v___x_2852_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
                    crate::leanh::lean_dec(v_basis_2851_);
                    if crate::leanh::lean_obj_tag(v___x_2853_) == 0 {
                        v_isSharedCheck_2860_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2853_)) as u8;
                        if v_isSharedCheck_2860_ == 0 {
                            v_unused_2861_ = crate::leanh::lean_ctor_get(v___x_2853_, 0);
                            crate::leanh::lean_dec(v_unused_2861_);
                            v___x_2855_ = v___x_2853_;
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2853_);
                            v___x_2855_ = crate::leanh::lean_box(0);
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2853_;
                    }
                } else {
                    v_a_2862_ = crate::leanh::lean_ctor_get(v___x_2849_, 0);
                    v_isSharedCheck_2869_ = (!crate::leanh::lean_is_exclusive(v___x_2849_)) as u8;
                    if v_isSharedCheck_2869_ == 0 {
                        v___x_2864_ = v___x_2849_;
                        v_isShared_2865_ = v_isSharedCheck_2869_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2862_);
                        crate::leanh::lean_dec(v___x_2849_);
                        v___x_2864_ = crate::leanh::lean_box(0);
                        v_isShared_2865_ = v_isSharedCheck_2869_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2852_);
                    v___x_2858_ = v___x_2855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2852_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2858_;
            }
            3 => {
                if v_isShared_2865_ == 0 {
                    v___x_2867_ = v___x_2864_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
                    v___x_2867_ = v_reuseFailAlloc_2868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis___boxed(
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
    mut v_a_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2882_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
        v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_,
        v_a_2878_, v_a_2879_, v_a_2880_,
    );
    crate::leanh::lean_dec(v_a_2880_);
    crate::leanh::lean_dec_ref(v_a_2879_);
    crate::leanh::lean_dec(v_a_2878_);
    crate::leanh::lean_dec_ref(v_a_2877_);
    crate::leanh::lean_dec(v_a_2876_);
    crate::leanh::lean_dec_ref(v_a_2875_);
    crate::leanh::lean_dec(v_a_2874_);
    crate::leanh::lean_dec_ref(v_a_2873_);
    crate::leanh::lean_dec(v_a_2872_);
    crate::leanh::lean_dec(v_a_2871_);
    crate::leanh::lean_dec(v_a_2870_);
    return v_res_2882_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(
    mut v_as_2883_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2884_: *mut crate::leanh::LeanObject,
    mut v_b_2885_: *mut crate::leanh::LeanObject,
    mut v_a_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2899_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_2884_, v_b_2885_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
    return v___x_2899_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(
    mut v_as_2900_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2901_: *mut crate::leanh::LeanObject,
    mut v_b_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
    mut v___y_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(v_as_2900_, v_as_x27_2901_, v_b_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
    crate::leanh::lean_dec(v___y_2914_);
    crate::leanh::lean_dec_ref(v___y_2913_);
    crate::leanh::lean_dec(v___y_2912_);
    crate::leanh::lean_dec_ref(v___y_2911_);
    crate::leanh::lean_dec(v___y_2910_);
    crate::leanh::lean_dec_ref(v___y_2909_);
    crate::leanh::lean_dec(v___y_2908_);
    crate::leanh::lean_dec_ref(v___y_2907_);
    crate::leanh::lean_dec(v___y_2906_);
    crate::leanh::lean_dec(v___y_2905_);
    crate::leanh::lean_dec(v___y_2904_);
    crate::leanh::lean_dec(v_as_x27_2901_);
    crate::leanh::lean_dec(v_as_2900_);
    return v_res_2916_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(
    mut v_init_2917_: *mut crate::leanh::LeanObject,
    mut v_x_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2918_) == 0 {
                    v_k_2931_ = crate::leanh::lean_ctor_get(v_x_2918_, 1);
                    v_l_2932_ = crate::leanh::lean_ctor_get(v_x_2918_, 3);
                    v_r_2933_ = crate::leanh::lean_ctor_get(v_x_2918_, 4);
                    v___x_2934_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_2917_, v_l_2932_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                    if crate::leanh::lean_obj_tag(v___x_2934_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2934_, 1);
                        v_lhs_2935_ = crate::leanh::lean_ctor_get(v_k_2931_, 0);
                        v_rhs_2936_ = crate::leanh::lean_ctor_get(v_k_2931_, 1);
                        v___x_2937_ = 0;
                        v___x_2938_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_2935_, v_rhs_2936_, v___x_2937_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                        if crate::leanh::lean_obj_tag(v___x_2938_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2938_, 1);
                            v___x_2939_ = crate::leanh::lean_box(0);
                            v_init_2917_ = v___x_2939_;
                            v_x_2918_ = v_r_2933_;
                            state = 0;
                            continue;
                        } else {
                            v_a_2941_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                            v_isSharedCheck_2948_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2938_)) as u8;
                            if v_isSharedCheck_2948_ == 0 {
                                v___x_2943_ = v___x_2938_;
                                v_isShared_2944_ = v_isSharedCheck_2948_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2941_);
                                crate::leanh::lean_dec(v___x_2938_);
                                v___x_2943_ = crate::leanh::lean_box(0);
                                v_isShared_2944_ = v_isSharedCheck_2948_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2934_;
                    }
                } else {
                    v___x_2949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2949_, 0, v_init_2917_);
                    v___x_2950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2950_, 0, v___x_2949_);
                    return v___x_2950_;
                }
            }
            1 => {
                if v_isShared_2944_ == 0 {
                    v___x_2946_ = v___x_2943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
                    v___x_2946_ = v_reuseFailAlloc_2947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0___boxed(
    mut v_init_2951_: *mut crate::leanh::LeanObject,
    mut v_x_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_2951_, v_x_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
    crate::leanh::lean_dec(v___y_2963_);
    crate::leanh::lean_dec_ref(v___y_2962_);
    crate::leanh::lean_dec(v___y_2961_);
    crate::leanh::lean_dec_ref(v___y_2960_);
    crate::leanh::lean_dec(v___y_2959_);
    crate::leanh::lean_dec_ref(v___y_2958_);
    crate::leanh::lean_dec(v___y_2957_);
    crate::leanh::lean_dec_ref(v___y_2956_);
    crate::leanh::lean_dec(v___y_2955_);
    crate::leanh::lean_dec(v___y_2954_);
    crate::leanh::lean_dec(v___y_2953_);
    crate::leanh::lean_dec(v_x_2952_);
    return v_res_2965_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_,
                    v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_,
                );
                if crate::leanh::lean_obj_tag(v___x_2978_) == 0 {
                    v_a_2979_ = crate::leanh::lean_ctor_get(v___x_2978_, 0);
                    crate::leanh::lean_inc(v_a_2979_);
                    crate::leanh::lean_dec_ref_known(v___x_2978_, 1);
                    v_queue_2980_ = crate::leanh::lean_ctor_get(v_a_2979_, 14);
                    crate::leanh::lean_inc(v_queue_2980_);
                    crate::leanh::lean_dec(v_a_2979_);
                    v___x_2981_ = crate::leanh::lean_box(0);
                    v___x_2982_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v___x_2981_, v_queue_2980_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
                    crate::leanh::lean_dec(v_queue_2980_);
                    if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                        v_isSharedCheck_2989_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_2989_ == 0 {
                            v_unused_2990_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                            crate::leanh::lean_dec(v_unused_2990_);
                            v___x_2984_ = v___x_2982_;
                            v_isShared_2985_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2982_);
                            v___x_2984_ = crate::leanh::lean_box(0);
                            v_isShared_2985_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2991_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_2998_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_2998_ == 0 {
                            v___x_2993_ = v___x_2982_;
                            v_isShared_2994_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2991_);
                            crate::leanh::lean_dec(v___x_2982_);
                            v___x_2993_ = crate::leanh::lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2999_ = crate::leanh::lean_ctor_get(v___x_2978_, 0);
                    v_isSharedCheck_3006_ = (!crate::leanh::lean_is_exclusive(v___x_2978_)) as u8;
                    if v_isSharedCheck_3006_ == 0 {
                        v___x_3001_ = v___x_2978_;
                        v_isShared_3002_ = v_isSharedCheck_3006_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2999_);
                        crate::leanh::lean_dec(v___x_2978_);
                        v___x_3001_ = crate::leanh::lean_box(0);
                        v_isShared_3002_ = v_isSharedCheck_3006_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2984_, 0, v___x_2981_);
                    v___x_2987_ = v___x_2984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2981_);
                    v___x_2987_ = v_reuseFailAlloc_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2987_;
            }
            3 => {
                if v_isShared_2994_ == 0 {
                    v___x_2996_ = v___x_2993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
                    v___x_2996_ = v_reuseFailAlloc_2997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2996_;
            }
            5 => {
                if v_isShared_3002_ == 0 {
                    v___x_3004_ = v___x_3001_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
                    v___x_3004_ = v_reuseFailAlloc_3005_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue___boxed(
    mut v_a_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_a_3010_: *mut crate::leanh::LeanObject,
    mut v_a_3011_: *mut crate::leanh::LeanObject,
    mut v_a_3012_: *mut crate::leanh::LeanObject,
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3019_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
        v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_,
        v_a_3015_, v_a_3016_, v_a_3017_,
    );
    crate::leanh::lean_dec(v_a_3017_);
    crate::leanh::lean_dec_ref(v_a_3016_);
    crate::leanh::lean_dec(v_a_3015_);
    crate::leanh::lean_dec_ref(v_a_3014_);
    crate::leanh::lean_dec(v_a_3013_);
    crate::leanh::lean_dec_ref(v_a_3012_);
    crate::leanh::lean_dec(v_a_3011_);
    crate::leanh::lean_dec_ref(v_a_3010_);
    crate::leanh::lean_dec(v_a_3009_);
    crate::leanh::lean_dec(v_a_3008_);
    crate::leanh::lean_dec(v_a_3007_);
    return v_res_3019_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(
    mut v_as_3023_: *mut crate::leanh::LeanObject,
    mut v_sz_3024_: usize,
    mut v_i_3025_: usize,
    mut v_b_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
    mut v___y_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: usize = 0;
    let mut v___x_3047_: usize = 0;
    let mut v_a_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3039_ = lean_usize_dec_lt(v_i_3025_, v_sz_3024_);
                if v___x_3039_ == 0 {
                    v___x_3040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3040_, 0, v_b_3026_);
                    return v___x_3040_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3026_);
                    v_a_3041_ = lean_array_uget_borrowed(v_as_3023_, v_i_3025_);
                    v_lhs_3042_ = crate::leanh::lean_ctor_get(v_a_3041_, 0);
                    v_rhs_3043_ = crate::leanh::lean_ctor_get(v_a_3041_, 1);
                    v___x_3044_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
                            v_lhs_3042_,
                            v_rhs_3043_,
                            v___x_3039_,
                            v___y_3027_,
                            v___y_3028_,
                            v___y_3029_,
                            v___y_3030_,
                            v___y_3031_,
                            v___y_3032_,
                            v___y_3033_,
                            v___y_3034_,
                            v___y_3035_,
                            v___y_3036_,
                            v___y_3037_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3044_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3044_, 1);
                        v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3046_ = 1usize;
                        v___x_3047_ = lean_usize_add(v_i_3025_, v___x_3046_);
                        v_i_3025_ = v___x_3047_;
                        v_b_3026_ = v___x_3045_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3049_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                        v_isSharedCheck_3056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3044_)) as u8;
                        if v_isSharedCheck_3056_ == 0 {
                            v___x_3051_ = v___x_3044_;
                            v_isShared_3052_ = v_isSharedCheck_3056_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3049_);
                            crate::leanh::lean_dec(v___x_3044_);
                            v___x_3051_ = crate::leanh::lean_box(0);
                            v_isShared_3052_ = v_isSharedCheck_3056_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3052_ == 0 {
                    v___x_3054_ = v___x_3051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___boxed(
    mut v_as_3057_: *mut crate::leanh::LeanObject,
    mut v_sz_3058_: *mut crate::leanh::LeanObject,
    mut v_i_3059_: *mut crate::leanh::LeanObject,
    mut v_b_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3073_: usize = 0;
    let mut v_i_boxed_3074_: usize = 0;
    let mut v_res_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3073_ = crate::leanh::lean_unbox_usize(v_sz_3058_);
    crate::leanh::lean_dec(v_sz_3058_);
    v_i_boxed_3074_ = crate::leanh::lean_unbox_usize(v_i_3059_);
    crate::leanh::lean_dec(v_i_3059_);
    v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_3057_, v_sz_boxed_3073_, v_i_boxed_3074_, v_b_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
    crate::leanh::lean_dec(v___y_3071_);
    crate::leanh::lean_dec_ref(v___y_3070_);
    crate::leanh::lean_dec(v___y_3069_);
    crate::leanh::lean_dec_ref(v___y_3068_);
    crate::leanh::lean_dec(v___y_3067_);
    crate::leanh::lean_dec_ref(v___y_3066_);
    crate::leanh::lean_dec(v___y_3065_);
    crate::leanh::lean_dec_ref(v___y_3064_);
    crate::leanh::lean_dec(v___y_3063_);
    crate::leanh::lean_dec(v___y_3062_);
    crate::leanh::lean_dec(v___y_3061_);
    crate::leanh::lean_dec_ref(v_as_3057_);
    return v_res_3075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(
    mut v_as_3076_: *mut crate::leanh::LeanObject,
    mut v_sz_3077_: usize,
    mut v_i_3078_: usize,
    mut v_b_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
    mut v___y_3081_: *mut crate::leanh::LeanObject,
    mut v___y_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: usize = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_usize_dec_lt(v_i_3078_, v_sz_3077_);
                if v___x_3092_ == 0 {
                    v___x_3093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3093_, 0, v_b_3079_);
                    return v___x_3093_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3079_);
                    v_a_3094_ = lean_array_uget_borrowed(v_as_3076_, v_i_3078_);
                    v_lhs_3095_ = crate::leanh::lean_ctor_get(v_a_3094_, 0);
                    v_rhs_3096_ = crate::leanh::lean_ctor_get(v_a_3094_, 1);
                    v___x_3097_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
                            v_lhs_3095_,
                            v_rhs_3096_,
                            v___x_3092_,
                            v___y_3080_,
                            v___y_3081_,
                            v___y_3082_,
                            v___y_3083_,
                            v___y_3084_,
                            v___y_3085_,
                            v___y_3086_,
                            v___y_3087_,
                            v___y_3088_,
                            v___y_3089_,
                            v___y_3090_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3097_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3097_, 1);
                        v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3099_ = 1usize;
                        v___x_3100_ = lean_usize_add(v_i_3078_, v___x_3099_);
                        v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_3076_, v_sz_3077_, v___x_3100_, v___x_3098_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
                        return v___x_3101_;
                    } else {
                        v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                        v_isSharedCheck_3109_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3097_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v___x_3104_ = v___x_3097_;
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3102_);
                            crate::leanh::lean_dec(v___x_3097_);
                            v___x_3104_ = crate::leanh::lean_box(0);
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3105_ == 0 {
                    v___x_3107_ = v___x_3104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1___boxed(
    mut v_as_3110_: *mut crate::leanh::LeanObject,
    mut v_sz_3111_: *mut crate::leanh::LeanObject,
    mut v_i_3112_: *mut crate::leanh::LeanObject,
    mut v_b_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3126_: usize = 0;
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_res_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3126_ = crate::leanh::lean_unbox_usize(v_sz_3111_);
    crate::leanh::lean_dec(v_sz_3111_);
    v_i_boxed_3127_ = crate::leanh::lean_unbox_usize(v_i_3112_);
    crate::leanh::lean_dec(v_i_3112_);
    v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_as_3110_, v_sz_boxed_3126_, v_i_boxed_3127_, v_b_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
    crate::leanh::lean_dec(v___y_3124_);
    crate::leanh::lean_dec_ref(v___y_3123_);
    crate::leanh::lean_dec(v___y_3122_);
    crate::leanh::lean_dec_ref(v___y_3121_);
    crate::leanh::lean_dec(v___y_3120_);
    crate::leanh::lean_dec_ref(v___y_3119_);
    crate::leanh::lean_dec(v___y_3118_);
    crate::leanh::lean_dec_ref(v___y_3117_);
    crate::leanh::lean_dec(v___y_3116_);
    crate::leanh::lean_dec(v___y_3115_);
    crate::leanh::lean_dec(v___y_3114_);
    crate::leanh::lean_dec_ref(v_as_3110_);
    return v_res_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(
    mut v_as_3132_: *mut crate::leanh::LeanObject,
    mut v_sz_3133_: usize,
    mut v_i_3134_: usize,
    mut v_b_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: usize = 0;
    let mut v___x_3156_: usize = 0;
    let mut v_a_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3161_: u8 = 0;
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3148_ = lean_usize_dec_lt(v_i_3134_, v_sz_3133_);
                if v___x_3148_ == 0 {
                    v___x_3149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3149_, 0, v_b_3135_);
                    return v___x_3149_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3135_);
                    v_a_3150_ = lean_array_uget_borrowed(v_as_3132_, v_i_3134_);
                    v_lhs_3151_ = crate::leanh::lean_ctor_get(v_a_3150_, 0);
                    v_rhs_3152_ = crate::leanh::lean_ctor_get(v_a_3150_, 1);
                    v___x_3153_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
                            v_lhs_3151_,
                            v_rhs_3152_,
                            v___x_3148_,
                            v___y_3136_,
                            v___y_3137_,
                            v___y_3138_,
                            v___y_3139_,
                            v___y_3140_,
                            v___y_3141_,
                            v___y_3142_,
                            v___y_3143_,
                            v___y_3144_,
                            v___y_3145_,
                            v___y_3146_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3153_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3153_, 1);
                        v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_3155_ = 1usize;
                        v___x_3156_ = lean_usize_add(v_i_3134_, v___x_3155_);
                        v_i_3134_ = v___x_3156_;
                        v_b_3135_ = v___x_3154_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3158_ = crate::leanh::lean_ctor_get(v___x_3153_, 0);
                        v_isSharedCheck_3165_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3153_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3160_ = v___x_3153_;
                            v_isShared_3161_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3158_);
                            crate::leanh::lean_dec(v___x_3153_);
                            v___x_3160_ = crate::leanh::lean_box(0);
                            v_isShared_3161_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3161_ == 0 {
                    v___x_3163_ = v___x_3160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_3166_: *mut crate::leanh::LeanObject,
    mut v_sz_3167_: *mut crate::leanh::LeanObject,
    mut v_i_3168_: *mut crate::leanh::LeanObject,
    mut v_b_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
    mut v___y_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3182_: usize = 0;
    let mut v_i_boxed_3183_: usize = 0;
    let mut v_res_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3182_ = crate::leanh::lean_unbox_usize(v_sz_3167_);
    crate::leanh::lean_dec(v_sz_3167_);
    v_i_boxed_3183_ = crate::leanh::lean_unbox_usize(v_i_3168_);
    crate::leanh::lean_dec(v_i_3168_);
    v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_3166_, v_sz_boxed_3182_, v_i_boxed_3183_, v_b_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
    crate::leanh::lean_dec(v___y_3180_);
    crate::leanh::lean_dec_ref(v___y_3179_);
    crate::leanh::lean_dec(v___y_3178_);
    crate::leanh::lean_dec_ref(v___y_3177_);
    crate::leanh::lean_dec(v___y_3176_);
    crate::leanh::lean_dec_ref(v___y_3175_);
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    crate::leanh::lean_dec(v___y_3172_);
    crate::leanh::lean_dec(v___y_3171_);
    crate::leanh::lean_dec(v___y_3170_);
    crate::leanh::lean_dec_ref(v_as_3166_);
    return v_res_3184_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(
    mut v_as_3185_: *mut crate::leanh::LeanObject,
    mut v_sz_3186_: usize,
    mut v_i_3187_: usize,
    mut v_b_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3201_ = lean_usize_dec_lt(v_i_3187_, v_sz_3186_);
                if v___x_3201_ == 0 {
                    v___x_3202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3202_, 0, v_b_3188_);
                    return v___x_3202_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3188_);
                    v_a_3203_ = lean_array_uget_borrowed(v_as_3185_, v_i_3187_);
                    v_lhs_3204_ = crate::leanh::lean_ctor_get(v_a_3203_, 0);
                    v_rhs_3205_ = crate::leanh::lean_ctor_get(v_a_3203_, 1);
                    v___x_3206_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
                            v_lhs_3204_,
                            v_rhs_3205_,
                            v___x_3201_,
                            v___y_3189_,
                            v___y_3190_,
                            v___y_3191_,
                            v___y_3192_,
                            v___y_3193_,
                            v___y_3194_,
                            v___y_3195_,
                            v___y_3196_,
                            v___y_3197_,
                            v___y_3198_,
                            v___y_3199_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3206_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3206_, 1);
                        v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_3208_ = 1usize;
                        v___x_3209_ = lean_usize_add(v_i_3187_, v___x_3208_);
                        v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_3185_, v_sz_3186_, v___x_3209_, v___x_3207_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
                        return v___x_3210_;
                    } else {
                        v_a_3211_ = crate::leanh::lean_ctor_get(v___x_3206_, 0);
                        v_isSharedCheck_3218_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3206_)) as u8;
                        if v_isSharedCheck_3218_ == 0 {
                            v___x_3213_ = v___x_3206_;
                            v_isShared_3214_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3211_);
                            crate::leanh::lean_dec(v___x_3206_);
                            v___x_3213_ = crate::leanh::lean_box(0);
                            v_isShared_3214_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3214_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2___boxed(
    mut v_as_3219_: *mut crate::leanh::LeanObject,
    mut v_sz_3220_: *mut crate::leanh::LeanObject,
    mut v_i_3221_: *mut crate::leanh::LeanObject,
    mut v_b_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3235_: usize = 0;
    let mut v_i_boxed_3236_: usize = 0;
    let mut v_res_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3235_ = crate::leanh::lean_unbox_usize(v_sz_3220_);
    crate::leanh::lean_dec(v_sz_3220_);
    v_i_boxed_3236_ = crate::leanh::lean_unbox_usize(v_i_3221_);
    crate::leanh::lean_dec(v_i_3221_);
    v_res_3237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_as_3219_, v_sz_boxed_3235_, v_i_boxed_3236_, v_b_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
    crate::leanh::lean_dec(v___y_3233_);
    crate::leanh::lean_dec_ref(v___y_3232_);
    crate::leanh::lean_dec(v___y_3231_);
    crate::leanh::lean_dec_ref(v___y_3230_);
    crate::leanh::lean_dec(v___y_3229_);
    crate::leanh::lean_dec_ref(v___y_3228_);
    crate::leanh::lean_dec(v___y_3227_);
    crate::leanh::lean_dec_ref(v___y_3226_);
    crate::leanh::lean_dec(v___y_3225_);
    crate::leanh::lean_dec(v___y_3224_);
    crate::leanh::lean_dec(v___y_3223_);
    crate::leanh::lean_dec_ref(v_as_3219_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(
    mut v_init_3238_: *mut crate::leanh::LeanObject,
    mut v_n_3239_: *mut crate::leanh::LeanObject,
    mut v_b_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3256_: usize = 0;
    let mut v___x_3257_: usize = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v_fst_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_vs_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3285_: usize = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v_fst_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_a_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3306_: u8 = 0;
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3239_) == 0 {
                    v_cs_3253_ = crate::leanh::lean_ctor_get(v_n_3239_, 0);
                    v___x_3254_ = crate::leanh::lean_box(0);
                    v___x_3255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                    crate::leanh::lean_ctor_set(v___x_3255_, 1, v_b_3240_);
                    v_sz_3256_ = lean_array_size(v_cs_3253_);
                    v___x_3257_ = 0usize;
                    v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_3238_, v_cs_3253_, v_sz_3256_, v___x_3257_, v___x_3255_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
                    if crate::leanh::lean_obj_tag(v___x_3258_) == 0 {
                        v_a_3259_ = crate::leanh::lean_ctor_get(v___x_3258_, 0);
                        v_isSharedCheck_3273_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3258_)) as u8;
                        if v_isSharedCheck_3273_ == 0 {
                            v___x_3261_ = v___x_3258_;
                            v_isShared_3262_ = v_isSharedCheck_3273_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3259_);
                            crate::leanh::lean_dec(v___x_3258_);
                            v___x_3261_ = crate::leanh::lean_box(0);
                            v_isShared_3262_ = v_isSharedCheck_3273_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3274_ = crate::leanh::lean_ctor_get(v___x_3258_, 0);
                        v_isSharedCheck_3281_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3258_)) as u8;
                        if v_isSharedCheck_3281_ == 0 {
                            v___x_3276_ = v___x_3258_;
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3274_);
                            crate::leanh::lean_dec(v___x_3258_);
                            v___x_3276_ = crate::leanh::lean_box(0);
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3282_ = crate::leanh::lean_ctor_get(v_n_3239_, 0);
                    v___x_3283_ = crate::leanh::lean_box(0);
                    v___x_3284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3284_, 0, v___x_3283_);
                    crate::leanh::lean_ctor_set(v___x_3284_, 1, v_b_3240_);
                    v_sz_3285_ = lean_array_size(v_vs_3282_);
                    v___x_3286_ = 0usize;
                    v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_vs_3282_, v_sz_3285_, v___x_3286_, v___x_3284_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
                    if crate::leanh::lean_obj_tag(v___x_3287_) == 0 {
                        v_a_3288_ = crate::leanh::lean_ctor_get(v___x_3287_, 0);
                        v_isSharedCheck_3302_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3287_)) as u8;
                        if v_isSharedCheck_3302_ == 0 {
                            v___x_3290_ = v___x_3287_;
                            v_isShared_3291_ = v_isSharedCheck_3302_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3288_);
                            crate::leanh::lean_dec(v___x_3287_);
                            v___x_3290_ = crate::leanh::lean_box(0);
                            v_isShared_3291_ = v_isSharedCheck_3302_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3303_ = crate::leanh::lean_ctor_get(v___x_3287_, 0);
                        v_isSharedCheck_3310_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3287_)) as u8;
                        if v_isSharedCheck_3310_ == 0 {
                            v___x_3305_ = v___x_3287_;
                            v_isShared_3306_ = v_isSharedCheck_3310_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3303_);
                            crate::leanh::lean_dec(v___x_3287_);
                            v___x_3305_ = crate::leanh::lean_box(0);
                            v_isShared_3306_ = v_isSharedCheck_3310_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3263_ = crate::leanh::lean_ctor_get(v_a_3259_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3263_) == 0 {
                    v_snd_3264_ = crate::leanh::lean_ctor_get(v_a_3259_, 1);
                    crate::leanh::lean_inc(v_snd_3264_);
                    crate::leanh::lean_dec(v_a_3259_);
                    v___x_3265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3265_, 0, v_snd_3264_);
                    if v_isShared_3262_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3261_, 0, v___x_3265_);
                        v___x_3267_ = v___x_3261_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
                        v___x_3267_ = v_reuseFailAlloc_3268_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3263_);
                    crate::leanh::lean_dec(v_a_3259_);
                    v_val_3269_ = crate::leanh::lean_ctor_get(v_fst_3263_, 0);
                    crate::leanh::lean_inc(v_val_3269_);
                    crate::leanh::lean_dec_ref_known(v_fst_3263_, 1);
                    if v_isShared_3262_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3261_, 0, v_val_3269_);
                        v___x_3271_ = v___x_3261_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_val_3269_);
                        v___x_3271_ = v_reuseFailAlloc_3272_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3267_;
            }
            3 => {
                return v___x_3271_;
            }
            4 => {
                if v_isShared_3277_ == 0 {
                    v___x_3279_ = v___x_3276_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3279_;
            }
            6 => {
                v_fst_3292_ = crate::leanh::lean_ctor_get(v_a_3288_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3292_) == 0 {
                    v_snd_3293_ = crate::leanh::lean_ctor_get(v_a_3288_, 1);
                    crate::leanh::lean_inc(v_snd_3293_);
                    crate::leanh::lean_dec(v_a_3288_);
                    v___x_3294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3294_, 0, v_snd_3293_);
                    if v_isShared_3291_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3290_, 0, v___x_3294_);
                        v___x_3296_ = v___x_3290_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
                        v___x_3296_ = v_reuseFailAlloc_3297_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3292_);
                    crate::leanh::lean_dec(v_a_3288_);
                    v_val_3298_ = crate::leanh::lean_ctor_get(v_fst_3292_, 0);
                    crate::leanh::lean_inc(v_val_3298_);
                    crate::leanh::lean_dec_ref_known(v_fst_3292_, 1);
                    if v_isShared_3291_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3290_, 0, v_val_3298_);
                        v___x_3300_ = v___x_3290_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3296_;
            }
            8 => {
                return v___x_3300_;
            }
            9 => {
                if v_isShared_3306_ == 0 {
                    v___x_3308_ = v___x_3305_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
                    v___x_3308_ = v_reuseFailAlloc_3309_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(
    mut v_init_3311_: *mut crate::leanh::LeanObject,
    mut v_as_3312_: *mut crate::leanh::LeanObject,
    mut v_sz_3313_: usize,
    mut v_i_3314_: usize,
    mut v_b_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v_reuseFailAlloc_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_usize_dec_lt(v_i_3314_, v_sz_3313_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3329_, 0, v_b_3315_);
                    return v___x_3329_;
                } else {
                    v_snd_3330_ = crate::leanh::lean_ctor_get(v_b_3315_, 1);
                    v_isSharedCheck_3364_ = (!crate::leanh::lean_is_exclusive(v_b_3315_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v_unused_3365_ = crate::leanh::lean_ctor_get(v_b_3315_, 0);
                        crate::leanh::lean_dec(v_unused_3365_);
                        v___x_3332_ = v_b_3315_;
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3330_);
                        crate::leanh::lean_dec(v_b_3315_);
                        v___x_3332_ = crate::leanh::lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3334_ = lean_array_uget_borrowed(v_as_3312_, v_i_3314_);
                crate::leanh::lean_inc(v_snd_3330_);
                v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3311_, v_a_3334_, v_snd_3330_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
                if crate::leanh::lean_obj_tag(v___x_3335_) == 0 {
                    v_a_3336_ = crate::leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3355_ = (!crate::leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3338_ = v___x_3335_;
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3336_);
                        crate::leanh::lean_dec(v___x_3335_);
                        v___x_3338_ = crate::leanh::lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3332_);
                    crate::leanh::lean_dec(v_snd_3330_);
                    v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3363_ = (!crate::leanh::lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3335_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3356_);
                        crate::leanh::lean_dec(v___x_3335_);
                        v___x_3358_ = crate::leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3340_, 0, v_a_3336_);
                    if v_isShared_3333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3330_);
                        v___x_3342_ = v_reuseFailAlloc_3346_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3338_);
                    crate::leanh::lean_dec(v_snd_3330_);
                    v_a_3347_ = crate::leanh::lean_ctor_get(v_a_3336_, 0);
                    crate::leanh::lean_inc(v_a_3347_);
                    crate::leanh::lean_dec_ref_known(v_a_3336_, 1);
                    v___x_3348_ = crate::leanh::lean_box(0);
                    if v_isShared_3333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3332_, 1, v_a_3347_);
                        crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3347_);
                        v___x_3350_ = v_reuseFailAlloc_3354_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3338_, 0, v___x_3342_);
                    v___x_3344_ = v___x_3338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
                    v___x_3344_ = v_reuseFailAlloc_3345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3344_;
            }
            5 => {
                v___x_3351_ = 1usize;
                v___x_3352_ = lean_usize_add(v_i_3314_, v___x_3351_);
                v_i_3314_ = v___x_3352_;
                v_b_3315_ = v___x_3350_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3359_ == 0 {
                    v___x_3361_ = v___x_3358_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_3366_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_3367_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_3368_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_3369_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_3370_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_3371_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_3372_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_3373_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3374_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3375_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3376_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3377_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3378_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3379_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3380_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3381_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3382_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_3383_: usize = 0;
    let mut v_i_boxed_3384_: usize = 0;
    let mut v_res_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3383_ = crate::leanh::lean_unbox_usize(v_sz_3368_);
    crate::leanh::lean_dec(v_sz_3368_);
    v_i_boxed_3384_ = crate::leanh::lean_unbox_usize(v_i_3369_);
    crate::leanh::lean_dec(v_i_3369_);
    v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_3366_, v_as_3367_, v_sz_boxed_3383_, v_i_boxed_3384_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec_ref(v___y_3380_);
    crate::leanh::lean_dec(v___y_3379_);
    crate::leanh::lean_dec_ref(v___y_3378_);
    crate::leanh::lean_dec(v___y_3377_);
    crate::leanh::lean_dec_ref(v___y_3376_);
    crate::leanh::lean_dec(v___y_3375_);
    crate::leanh::lean_dec_ref(v___y_3374_);
    crate::leanh::lean_dec(v___y_3373_);
    crate::leanh::lean_dec(v___y_3372_);
    crate::leanh::lean_dec(v___y_3371_);
    crate::leanh::lean_dec_ref(v_as_3367_);
    return v_res_3385_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(
    mut v_init_3386_: *mut crate::leanh::LeanObject,
    mut v_n_3387_: *mut crate::leanh::LeanObject,
    mut v_b_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3386_, v_n_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
    crate::leanh::lean_dec(v___y_3399_);
    crate::leanh::lean_dec_ref(v___y_3398_);
    crate::leanh::lean_dec(v___y_3397_);
    crate::leanh::lean_dec_ref(v___y_3396_);
    crate::leanh::lean_dec(v___y_3395_);
    crate::leanh::lean_dec_ref(v___y_3394_);
    crate::leanh::lean_dec(v___y_3393_);
    crate::leanh::lean_dec_ref(v___y_3392_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec(v___y_3390_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v_n_3387_);
    return v_res_3401_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(
    mut v_t_3402_: *mut crate::leanh::LeanObject,
    mut v_init_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v_a_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v_fst_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_a_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3416_ = crate::leanh::lean_ctor_get(v_t_3402_, 0);
                v_tail_3417_ = crate::leanh::lean_ctor_get(v_t_3402_, 1);
                v___x_3418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3403_, v_root_3416_, v_init_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
                if crate::leanh::lean_obj_tag(v___x_3418_) == 0 {
                    v_a_3419_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3455_ = (!crate::leanh::lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3421_ = v___x_3418_;
                        v_isShared_3422_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3419_);
                        crate::leanh::lean_dec(v___x_3418_);
                        v___x_3421_ = crate::leanh::lean_box(0);
                        v_isShared_3422_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3456_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3463_ = (!crate::leanh::lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3458_ = v___x_3418_;
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3456_);
                        crate::leanh::lean_dec(v___x_3418_);
                        v___x_3458_ = crate::leanh::lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3419_) == 0 {
                    v_a_3423_ = crate::leanh::lean_ctor_get(v_a_3419_, 0);
                    crate::leanh::lean_inc(v_a_3423_);
                    crate::leanh::lean_dec_ref_known(v_a_3419_, 1);
                    if v_isShared_3422_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3421_, 0, v_a_3423_);
                        v___x_3425_ = v___x_3421_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3423_);
                        v___x_3425_ = v_reuseFailAlloc_3426_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3421_);
                    v_a_3427_ = crate::leanh::lean_ctor_get(v_a_3419_, 0);
                    crate::leanh::lean_inc(v_a_3427_);
                    crate::leanh::lean_dec_ref_known(v_a_3419_, 1);
                    v___x_3428_ = crate::leanh::lean_box(0);
                    v___x_3429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3429_, 0, v___x_3428_);
                    crate::leanh::lean_ctor_set(v___x_3429_, 1, v_a_3427_);
                    v_sz_3430_ = lean_array_size(v_tail_3417_);
                    v___x_3431_ = 0usize;
                    v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_tail_3417_, v_sz_3430_, v___x_3431_, v___x_3429_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
                    if crate::leanh::lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = crate::leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3446_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3446_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3433_);
                            crate::leanh::lean_dec(v___x_3432_);
                            v___x_3435_ = crate::leanh::lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3447_ = crate::leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3454_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3454_ == 0 {
                            v___x_3449_ = v___x_3432_;
                            v_isShared_3450_ = v_isSharedCheck_3454_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3447_);
                            crate::leanh::lean_dec(v___x_3432_);
                            v___x_3449_ = crate::leanh::lean_box(0);
                            v_isShared_3450_ = v_isSharedCheck_3454_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3425_;
            }
            3 => {
                v_fst_3437_ = crate::leanh::lean_ctor_get(v_a_3433_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3437_) == 0 {
                    v_snd_3438_ = crate::leanh::lean_ctor_get(v_a_3433_, 1);
                    crate::leanh::lean_inc(v_snd_3438_);
                    crate::leanh::lean_dec(v_a_3433_);
                    if v_isShared_3436_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3435_, 0, v_snd_3438_);
                        v___x_3440_ = v___x_3435_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_snd_3438_);
                        v___x_3440_ = v_reuseFailAlloc_3441_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3437_);
                    crate::leanh::lean_dec(v_a_3433_);
                    v_val_3442_ = crate::leanh::lean_ctor_get(v_fst_3437_, 0);
                    crate::leanh::lean_inc(v_val_3442_);
                    crate::leanh::lean_dec_ref_known(v_fst_3437_, 1);
                    if v_isShared_3436_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3435_, 0, v_val_3442_);
                        v___x_3444_ = v___x_3435_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_val_3442_);
                        v___x_3444_ = v_reuseFailAlloc_3445_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3440_;
            }
            5 => {
                return v___x_3444_;
            }
            6 => {
                if v_isShared_3450_ == 0 {
                    v___x_3452_ = v___x_3449_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3452_;
            }
            8 => {
                if v_isShared_3459_ == 0 {
                    v___x_3461_ = v___x_3458_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
                    v___x_3461_ = v_reuseFailAlloc_3462_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0___boxed(
    mut v_t_3464_: *mut crate::leanh::LeanObject,
    mut v_init_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_t_3464_, v_init_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
    crate::leanh::lean_dec(v___y_3476_);
    crate::leanh::lean_dec_ref(v___y_3475_);
    crate::leanh::lean_dec(v___y_3474_);
    crate::leanh::lean_dec_ref(v___y_3473_);
    crate::leanh::lean_dec(v___y_3472_);
    crate::leanh::lean_dec_ref(v___y_3471_);
    crate::leanh::lean_dec(v___y_3470_);
    crate::leanh::lean_dec_ref(v___y_3469_);
    crate::leanh::lean_dec(v___y_3468_);
    crate::leanh::lean_dec(v___y_3467_);
    crate::leanh::lean_dec(v___y_3466_);
    crate::leanh::lean_dec_ref(v_t_3464_);
    return v_res_3478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(
    mut v_a_3479_: *mut crate::leanh::LeanObject,
    mut v_a_3480_: *mut crate::leanh::LeanObject,
    mut v_a_3481_: *mut crate::leanh::LeanObject,
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
    mut v_a_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v_unused_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3491_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_,
                    v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_,
                );
                if crate::leanh::lean_obj_tag(v___x_3491_) == 0 {
                    v_a_3492_ = crate::leanh::lean_ctor_get(v___x_3491_, 0);
                    crate::leanh::lean_inc(v_a_3492_);
                    crate::leanh::lean_dec_ref_known(v___x_3491_, 1);
                    v_diseqs_3493_ = crate::leanh::lean_ctor_get(v_a_3492_, 16);
                    crate::leanh::lean_inc_ref(v_diseqs_3493_);
                    crate::leanh::lean_dec(v_a_3492_);
                    v___x_3494_ = crate::leanh::lean_box(0);
                    v___x_3495_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_diseqs_3493_, v___x_3494_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
                    crate::leanh::lean_dec_ref(v_diseqs_3493_);
                    if crate::leanh::lean_obj_tag(v___x_3495_) == 0 {
                        v_isSharedCheck_3502_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3495_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v_unused_3503_ = crate::leanh::lean_ctor_get(v___x_3495_, 0);
                            crate::leanh::lean_dec(v_unused_3503_);
                            v___x_3497_ = v___x_3495_;
                            v_isShared_3498_ = v_isSharedCheck_3502_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3495_);
                            v___x_3497_ = crate::leanh::lean_box(0);
                            v_isShared_3498_ = v_isSharedCheck_3502_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3495_;
                    }
                } else {
                    v_a_3504_ = crate::leanh::lean_ctor_get(v___x_3491_, 0);
                    v_isSharedCheck_3511_ = (!crate::leanh::lean_is_exclusive(v___x_3491_)) as u8;
                    if v_isSharedCheck_3511_ == 0 {
                        v___x_3506_ = v___x_3491_;
                        v_isShared_3507_ = v_isSharedCheck_3511_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3504_);
                        crate::leanh::lean_dec(v___x_3491_);
                        v___x_3506_ = crate::leanh::lean_box(0);
                        v_isShared_3507_ = v_isSharedCheck_3511_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3494_);
                    v___x_3500_ = v___x_3497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3494_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3500_;
            }
            3 => {
                if v_isShared_3507_ == 0 {
                    v___x_3509_ = v___x_3506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
                    v___x_3509_ = v_reuseFailAlloc_3510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs___boxed(
    mut v_a_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
    mut v_a_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3524_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(
        v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_,
        v_a_3520_, v_a_3521_, v_a_3522_,
    );
    crate::leanh::lean_dec(v_a_3522_);
    crate::leanh::lean_dec_ref(v_a_3521_);
    crate::leanh::lean_dec(v_a_3520_);
    crate::leanh::lean_dec_ref(v_a_3519_);
    crate::leanh::lean_dec(v_a_3518_);
    crate::leanh::lean_dec_ref(v_a_3517_);
    crate::leanh::lean_dec(v_a_3516_);
    crate::leanh::lean_dec_ref(v_a_3515_);
    crate::leanh::lean_dec(v_a_3514_);
    crate::leanh::lean_dec(v_a_3513_);
    crate::leanh::lean_dec(v_a_3512_);
    return v_res_3524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(
        v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_,
        v_a_3533_, v_a_3534_, v_a_3535_,
    );
    if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
        let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3537_, 1);
        v___x_3538_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
            v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_,
            v_a_3533_, v_a_3534_, v_a_3535_,
        );
        if crate::leanh::lean_obj_tag(v___x_3538_) == 0 {
            let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3538_, 1);
            v___x_3539_ =
                l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
                    v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_,
                    v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_,
                );
            if crate::leanh::lean_obj_tag(v___x_3539_) == 0 {
                let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_3539_, 1);
                v___x_3540_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(
                        v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_,
                        v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_,
                    );
                return v___x_3540_;
            } else {
                return v___x_3539_;
            }
        } else {
            return v___x_3538_;
        }
    } else {
        return v___x_3537_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs___boxed(
    mut v_a_3541_: *mut crate::leanh::LeanObject,
    mut v_a_3542_: *mut crate::leanh::LeanObject,
    mut v_a_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3553_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(
        v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_,
        v_a_3549_, v_a_3550_, v_a_3551_,
    );
    crate::leanh::lean_dec(v_a_3551_);
    crate::leanh::lean_dec_ref(v_a_3550_);
    crate::leanh::lean_dec(v_a_3549_);
    crate::leanh::lean_dec_ref(v_a_3548_);
    crate::leanh::lean_dec(v_a_3547_);
    crate::leanh::lean_dec_ref(v_a_3546_);
    crate::leanh::lean_dec(v_a_3545_);
    crate::leanh::lean_dec_ref(v_a_3544_);
    crate::leanh::lean_dec(v_a_3543_);
    crate::leanh::lean_dec(v_a_3542_);
    crate::leanh::lean_dec(v_a_3541_);
    return v_res_3553_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(
    mut v_upperBound_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_b_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3568_ = lean_nat_dec_lt(v_a_3555_, v_upperBound_3554_);
                if v___x_3568_ == 0 {
                    crate::leanh::lean_dec(v_a_3555_);
                    v___x_3569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3569_, 0, v_b_3556_);
                    return v___x_3569_;
                } else {
                    v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_3555_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
                    if crate::leanh::lean_obj_tag(v___x_3570_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3570_, 1);
                        v___x_3571_ = crate::leanh::lean_box(0);
                        v___x_3572_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3573_ = lean_nat_add(v_a_3555_, v___x_3572_);
                        crate::leanh::lean_dec(v_a_3555_);
                        v_a_3555_ = v___x_3573_;
                        v_b_3556_ = v___x_3571_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3555_);
                        return v___x_3570_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_b_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3589_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(
            v_upperBound_3575_,
            v_a_3576_,
            v_b_3577_,
            v___y_3578_,
            v___y_3579_,
            v___y_3580_,
            v___y_3581_,
            v___y_3582_,
            v___y_3583_,
            v___y_3584_,
            v___y_3585_,
            v___y_3586_,
            v___y_3587_,
        );
    crate::leanh::lean_dec(v___y_3587_);
    crate::leanh::lean_dec_ref(v___y_3586_);
    crate::leanh::lean_dec(v___y_3585_);
    crate::leanh::lean_dec_ref(v___y_3584_);
    crate::leanh::lean_dec(v___y_3583_);
    crate::leanh::lean_dec_ref(v___y_3582_);
    crate::leanh::lean_dec(v___y_3581_);
    crate::leanh::lean_dec_ref(v___y_3580_);
    crate::leanh::lean_dec(v___y_3579_);
    crate::leanh::lean_dec(v___y_3578_);
    crate::leanh::lean_dec(v_upperBound_3575_);
    return v_res_3589_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkInvariants(
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_debug_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_unused_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_3601_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3592_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_3601_ == 0 {
                    v___x_3602_ = crate::leanh::lean_box(0);
                    v___x_3603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3603_, 0, v___x_3602_);
                    return v___x_3603_;
                } else {
                    v___x_3604_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_3590_, v_a_3598_);
                    if crate::leanh::lean_obj_tag(v___x_3604_) == 0 {
                        v_a_3605_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                        crate::leanh::lean_inc(v_a_3605_);
                        crate::leanh::lean_dec_ref_known(v___x_3604_, 1);
                        v_structs_3606_ = crate::leanh::lean_ctor_get(v_a_3605_, 0);
                        crate::leanh::lean_inc_ref(v_structs_3606_);
                        crate::leanh::lean_dec(v_a_3605_);
                        v___x_3607_ = lean_array_get_size(v_structs_3606_);
                        crate::leanh::lean_dec_ref(v_structs_3606_);
                        v___x_3608_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3609_ = crate::leanh::lean_box(0);
                        v___x_3610_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v___x_3607_, v___x_3608_, v___x_3609_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
                        if crate::leanh::lean_obj_tag(v___x_3610_) == 0 {
                            v_isSharedCheck_3617_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                            if v_isSharedCheck_3617_ == 0 {
                                v_unused_3618_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                                crate::leanh::lean_dec(v_unused_3618_);
                                v___x_3612_ = v___x_3610_;
                                v_isShared_3613_ = v_isSharedCheck_3617_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3610_);
                                v___x_3612_ = crate::leanh::lean_box(0);
                                v_isShared_3613_ = v_isSharedCheck_3617_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3610_;
                        }
                    } else {
                        v_a_3619_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                        v_isSharedCheck_3626_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3604_)) as u8;
                        if v_isSharedCheck_3626_ == 0 {
                            v___x_3621_ = v___x_3604_;
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3619_);
                            crate::leanh::lean_dec(v___x_3604_);
                            v___x_3621_ = crate::leanh::lean_box(0);
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3609_);
                    v___x_3615_ = v___x_3612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3609_);
                    v___x_3615_ = v_reuseFailAlloc_3616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3615_;
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3625_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkInvariants___boxed(
    mut v_a_3627_: *mut crate::leanh::LeanObject,
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_3635_: *mut crate::leanh::LeanObject,
    mut v_a_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_Lean_Meta_Grind_AC_checkInvariants(
        v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_,
        v_a_3635_, v_a_3636_,
    );
    crate::leanh::lean_dec(v_a_3636_);
    crate::leanh::lean_dec_ref(v_a_3635_);
    crate::leanh::lean_dec(v_a_3634_);
    crate::leanh::lean_dec_ref(v_a_3633_);
    crate::leanh::lean_dec(v_a_3632_);
    crate::leanh::lean_dec_ref(v_a_3631_);
    crate::leanh::lean_dec(v_a_3630_);
    crate::leanh::lean_dec_ref(v_a_3629_);
    crate::leanh::lean_dec(v_a_3628_);
    crate::leanh::lean_dec(v_a_3627_);
    return v_res_3638_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(
    mut v_upperBound_3639_: *mut crate::leanh::LeanObject,
    mut v_inst_3640_: *mut crate::leanh::LeanObject,
    mut v_R_3641_: *mut crate::leanh::LeanObject,
    mut v_a_3642_: *mut crate::leanh::LeanObject,
    mut v_b_3643_: *mut crate::leanh::LeanObject,
    mut v_c_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
    mut v___y_3651_: *mut crate::leanh::LeanObject,
    mut v___y_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(
            v_upperBound_3639_,
            v_a_3642_,
            v_b_3643_,
            v___y_3645_,
            v___y_3646_,
            v___y_3647_,
            v___y_3648_,
            v___y_3649_,
            v___y_3650_,
            v___y_3651_,
            v___y_3652_,
            v___y_3653_,
            v___y_3654_,
        );
    return v___x_3656_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_3657_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_3658_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_R_3659_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_3660_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_3661_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_c_3662_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_3663_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_3664_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3665_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3666_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3667_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3668_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3669_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3670_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3671_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3672_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3673_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(
        v_upperBound_3657_,
        v_inst_3658_,
        v_R_3659_,
        v_a_3660_,
        v_b_3661_,
        v_c_3662_,
        v___y_3663_,
        v___y_3664_,
        v___y_3665_,
        v___y_3666_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
        v___y_3671_,
        v___y_3672_,
    );
    crate::leanh::lean_dec(v___y_3672_);
    crate::leanh::lean_dec_ref(v___y_3671_);
    crate::leanh::lean_dec(v___y_3670_);
    crate::leanh::lean_dec_ref(v___y_3669_);
    crate::leanh::lean_dec(v___y_3668_);
    crate::leanh::lean_dec_ref(v___y_3667_);
    crate::leanh::lean_dec(v___y_3666_);
    crate::leanh::lean_dec_ref(v___y_3665_);
    crate::leanh::lean_dec(v___y_3664_);
    crate::leanh::lean_dec(v___y_3663_);
    crate::leanh::lean_dec(v_upperBound_3657_);
    return v_res_3674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Inv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
}
