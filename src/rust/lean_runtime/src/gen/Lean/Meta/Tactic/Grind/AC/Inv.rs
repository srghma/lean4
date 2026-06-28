// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Inv
// Imports: Lean.Meta.Tactic.Grind.AC.Util Lean.Meta.Tactic.Grind.AC.Seq
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
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value: LeanStringObject<184> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 184, m_capacity: 184, m_length: 183, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 47, 45, 10, 42, 42, 78, 111, 116, 101, 42, 42, 58, 32, 69, 108, 101, 109, 101, 110, 116, 115, 32, 105, 110, 32, 116, 104, 101, 32, 116, 111, 100, 111, 32, 113, 117, 101, 117, 101, 32, 97, 114, 101, 32, 110, 111, 116, 32, 102, 117, 108, 108, 121, 32, 115, 105, 109, 112, 108, 105, 102, 105, 101, 100, 46, 10, 82, 101, 99, 97, 108, 108, 32, 116, 104, 97, 116, 32, 119, 101, 32, 111, 110, 108, 121, 32, 40, 102, 117, 108, 108, 121, 41, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 104, 101, 109, 32, 119, 104, 101, 110, 32, 97, 100, 100, 105, 110, 103, 32, 116, 104, 101, 109, 32, 116, 111, 32, 116, 104, 101, 32, 98, 97, 115, 105, 115, 46, 10, 45, 47, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 83, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 110, 111, 65, 100, 106, 97, 99, 101, 110, 116, 68, 117, 112, 108, 105, 99, 97, 116, 101, 115, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 115, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 48, 32, 124, 124, 32, 115, 32, 61, 61, 32, 46, 118, 97, 114, 32, 48, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 99, 104, 101, 99, 107, 66, 97, 115, 105, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 99, 111, 109, 112, 97, 114, 101, 32, 99, 46, 108, 104, 115, 32, 99, 46, 114, 104, 115, 32, 61, 61, 32, 46, 103, 116, 10, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_1838_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(
    mut v_msg_1839_: *mut LeanObject,
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
    mut v___y_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472__overap_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0);
    v___f_1853_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1853_, 0, v___x_1852_);
    v___x_5472__overap_1854_ = lean_panic_fn_borrowed(v___f_1853_, v_msg_1839_);
    lean_dec_ref(v___f_1853_);
    lean_inc(v___y_1850_);
    lean_inc_ref(v___y_1849_);
    lean_inc(v___y_1848_);
    lean_inc_ref(v___y_1847_);
    lean_inc(v___y_1846_);
    lean_inc_ref(v___y_1845_);
    lean_inc(v___y_1844_);
    lean_inc_ref(v___y_1843_);
    lean_inc(v___y_1842_);
    lean_inc(v___y_1841_);
    lean_inc(v___y_1840_);
    v___x_1855_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_1855_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___boxed(
    mut v_msg_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
    lean_dec(v___y_1867_);
    lean_dec_ref(v___y_1866_);
    lean_dec(v___y_1865_);
    lean_dec_ref(v___y_1864_);
    lean_dec(v___y_1863_);
    lean_dec_ref(v___y_1862_);
    lean_dec(v___y_1861_);
    lean_dec_ref(v___y_1860_);
    lean_dec(v___y_1859_);
    lean_dec(v___y_1858_);
    lean_dec(v___y_1857_);
    return v_res_1869_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_1870_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(
    mut v_msg_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
    mut v___y_1874_: *mut LeanObject,
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490__overap_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    v___x_1884_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0);
    v___f_1885_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1885_, 0, v___x_1884_);
    v___x_5490__overap_1886_ = lean_panic_fn_borrowed(v___f_1885_, v_msg_1871_);
    lean_dec_ref(v___f_1885_);
    lean_inc(v___y_1882_);
    lean_inc_ref(v___y_1881_);
    lean_inc(v___y_1880_);
    lean_inc_ref(v___y_1879_);
    lean_inc(v___y_1878_);
    lean_inc_ref(v___y_1877_);
    lean_inc(v___y_1876_);
    lean_inc_ref(v___y_1875_);
    lean_inc(v___y_1874_);
    lean_inc(v___y_1873_);
    lean_inc(v___y_1872_);
    v___x_1887_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_1887_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___boxed(
    mut v_msg_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1901_: *mut LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
    lean_dec(v___y_1899_);
    lean_dec_ref(v___y_1898_);
    lean_dec(v___y_1897_);
    lean_dec_ref(v___y_1896_);
    lean_dec(v___y_1895_);
    lean_dec_ref(v___y_1894_);
    lean_dec(v___y_1893_);
    lean_dec_ref(v___y_1892_);
    lean_dec(v___y_1891_);
    lean_dec(v___y_1890_);
    lean_dec(v___y_1889_);
    return v_res_1901_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2;
    v___x_1906_ = lean_unsigned_to_nat(6);
    v___x_1907_ = lean_unsigned_to_nat(21);
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
-> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4;
    v___x_1913_ = lean_unsigned_to_nat(6);
    v___x_1914_ = lean_unsigned_to_nat(19);
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
    mut v_vars_1918_: *mut LeanObject,
    mut v_x_1919_: *mut LeanObject,
    mut v_____s_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1938_ = lean_ctor_get(v_x_1919_, 0);
                v_snd_1939_ = lean_ctor_get(v_x_1919_, 1);
                v_size_1940_ = lean_ctor_get(v_vars_1918_, 2);
                v___x_1941_ = lean_nat_dec_lt(v_snd_1939_, v_size_1940_);
                if v___x_1941_ == 0 {
                    v___x_1942_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3);
                    v___x_1943_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_1942_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
                    if lean_obj_tag(v___x_1943_) == 0 {
                        lean_dec_ref_known(v___x_1943_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
                        v_isSharedCheck_1951_ = (!lean_is_exclusive(v___x_1943_)) as u8;
                        if v_isSharedCheck_1951_ == 0 {
                            v___x_1946_ = v___x_1943_;
                            v_isShared_1947_ = v_isSharedCheck_1951_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1944_);
                            lean_dec(v___x_1943_);
                            v___x_1946_ = lean_box(0);
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
                    lean_dec(v___x_1953_);
                    if v___x_1954_ == 0 {
                        v___x_1955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5);
                        v___x_1956_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v___x_1955_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
                        return v___x_1956_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1934_ = lean_unsigned_to_nat(1);
                v___x_1935_ = lean_nat_add(v_____s_1920_, v___x_1934_);
                v___x_1936_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1936_, 0, v___x_1935_);
                v___x_1937_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1937_, 0, v___x_1936_);
                return v___x_1937_;
            }
            2 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
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
    mut v_vars_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v_____s_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1972_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1970_);
    lean_dec_ref(v___y_1969_);
    lean_dec(v___y_1968_);
    lean_dec_ref(v___y_1967_);
    lean_dec(v___y_1966_);
    lean_dec_ref(v___y_1965_);
    lean_dec(v___y_1964_);
    lean_dec_ref(v___y_1963_);
    lean_dec(v___y_1962_);
    lean_dec(v___y_1961_);
    lean_dec(v___y_1960_);
    lean_dec(v_____s_1959_);
    lean_dec_ref(v_x_1958_);
    lean_dec_ref(v_vars_1957_);
    return v_res_1972_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(
    mut v_f_1973_: *mut LeanObject,
    mut v_s_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_b_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v_a_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut v_a_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1989_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1989_, 0, v_a_1975_);
                lean_ctor_set(v___x_1989_, 1, v_b_1976_);
                lean_inc(v___y_1987_);
                lean_inc_ref(v___y_1986_);
                lean_inc(v___y_1985_);
                lean_inc_ref(v___y_1984_);
                lean_inc(v___y_1983_);
                lean_inc_ref(v___y_1982_);
                lean_inc(v___y_1981_);
                lean_inc_ref(v___y_1980_);
                lean_inc(v___y_1979_);
                lean_inc(v___y_1978_);
                lean_inc(v___y_1977_);
                v___x_1990_ = lean_apply_14(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1990_) == 0 {
                    v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
                    v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_1993_ = v___x_1990_;
                        v_isShared_1994_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1991_);
                        lean_dec(v___x_1990_);
                        v___x_1993_ = lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2018_ = lean_ctor_get(v___x_1990_, 0);
                    v_isSharedCheck_2025_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2020_ = v___x_1990_;
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2018_);
                        lean_dec(v___x_1990_);
                        v___x_2020_ = lean_box(0);
                        v_isShared_2021_ = v_isSharedCheck_2025_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1991_) == 0 {
                    v_a_1995_ = lean_ctor_get(v_a_1991_, 0);
                    v_isSharedCheck_2005_ = (!lean_is_exclusive(v_a_1991_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1997_ = v_a_1991_;
                        v_isShared_1998_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1995_);
                        lean_dec(v_a_1991_);
                        v___x_1997_ = lean_box(0);
                        v_isShared_1998_ = v_isSharedCheck_2005_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2006_ = lean_ctor_get(v_a_1991_, 0);
                    v_isSharedCheck_2016_ = (!lean_is_exclusive(v_a_1991_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2008_ = v_a_1991_;
                        v_isShared_2009_ = v_isSharedCheck_2016_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2006_);
                        lean_dec(v_a_1991_);
                        v___x_2008_ = lean_box(0);
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
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1995_);
                    v___x_2000_ = v_reuseFailAlloc_2004_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1994_ == 0 {
                    lean_ctor_set(v___x_1993_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
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
                    v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2006_);
                    v___x_2011_ = v_reuseFailAlloc_2015_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1994_ == 0 {
                    lean_ctor_set(v___x_1993_, 0, v___x_2011_);
                    v___x_2013_ = v___x_1993_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
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
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
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
    mut v_f_2026_: *mut LeanObject,
    mut v_s_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_b_2029_: *mut LeanObject,
    mut v___y_2030_: *mut LeanObject,
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
    mut v___y_2033_: *mut LeanObject,
    mut v___y_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2042_: *mut LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(v_f_2026_, v_s_2027_, v_a_2028_, v_b_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
    lean_dec(v___y_2040_);
    lean_dec_ref(v___y_2039_);
    lean_dec(v___y_2038_);
    lean_dec_ref(v___y_2037_);
    lean_dec(v___y_2036_);
    lean_dec_ref(v___y_2035_);
    lean_dec(v___y_2034_);
    lean_dec_ref(v___y_2033_);
    lean_dec(v___y_2032_);
    lean_dec(v___y_2031_);
    lean_dec(v___y_2030_);
    return v_res_2042_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(
    mut v_f_2043_: *mut LeanObject,
    mut v_keys_2044_: *mut LeanObject,
    mut v_vals_2045_: *mut LeanObject,
    mut v_i_2046_: *mut LeanObject,
    mut v_acc_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_array_get_size(v_keys_2044_);
                v___x_2061_ = lean_nat_dec_lt(v_i_2046_, v___x_2060_);
                if v___x_2061_ == 0 {
                    lean_dec(v_i_2046_);
                    lean_dec_ref(v_f_2043_);
                    v___x_2062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2062_, 0, v_acc_2047_);
                    v___x_2063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2063_, 0, v___x_2062_);
                    return v___x_2063_;
                } else {
                    v_k_2064_ = lean_array_fget_borrowed(v_keys_2044_, v_i_2046_);
                    v_v_2065_ = lean_array_fget_borrowed(v_vals_2045_, v_i_2046_);
                    lean_inc_ref(v_f_2043_);
                    lean_inc(v___y_2058_);
                    lean_inc_ref(v___y_2057_);
                    lean_inc(v___y_2056_);
                    lean_inc_ref(v___y_2055_);
                    lean_inc(v___y_2054_);
                    lean_inc_ref(v___y_2053_);
                    lean_inc(v___y_2052_);
                    lean_inc_ref(v___y_2051_);
                    lean_inc(v___y_2050_);
                    lean_inc(v___y_2049_);
                    lean_inc(v___y_2048_);
                    lean_inc(v_v_2065_);
                    lean_inc(v_k_2064_);
                    v___x_2066_ = lean_apply_15(
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
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2066_) == 0 {
                        v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
                        lean_inc(v_a_2067_);
                        if lean_obj_tag(v_a_2067_) == 0 {
                            lean_dec_ref_known(v_a_2067_, 1);
                            lean_dec(v_i_2046_);
                            lean_dec_ref(v_f_2043_);
                            return v___x_2066_;
                        } else {
                            lean_dec_ref_known(v___x_2066_, 1);
                            v_a_2068_ = lean_ctor_get(v_a_2067_, 0);
                            lean_inc(v_a_2068_);
                            lean_dec_ref_known(v_a_2067_, 1);
                            v___x_2069_ = lean_unsigned_to_nat(1);
                            v___x_2070_ = lean_nat_add(v_i_2046_, v___x_2069_);
                            lean_dec(v_i_2046_);
                            v_i_2046_ = v___x_2070_;
                            v_acc_2047_ = v_a_2068_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_2046_);
                        lean_dec_ref(v_f_2043_);
                        return v___x_2066_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_2072_: *mut LeanObject = *_args.add(0);
    let mut v_keys_2073_: *mut LeanObject = *_args.add(1);
    let mut v_vals_2074_: *mut LeanObject = *_args.add(2);
    let mut v_i_2075_: *mut LeanObject = *_args.add(3);
    let mut v_acc_2076_: *mut LeanObject = *_args.add(4);
    let mut v___y_2077_: *mut LeanObject = *_args.add(5);
    let mut v___y_2078_: *mut LeanObject = *_args.add(6);
    let mut v___y_2079_: *mut LeanObject = *_args.add(7);
    let mut v___y_2080_: *mut LeanObject = *_args.add(8);
    let mut v___y_2081_: *mut LeanObject = *_args.add(9);
    let mut v___y_2082_: *mut LeanObject = *_args.add(10);
    let mut v___y_2083_: *mut LeanObject = *_args.add(11);
    let mut v___y_2084_: *mut LeanObject = *_args.add(12);
    let mut v___y_2085_: *mut LeanObject = *_args.add(13);
    let mut v___y_2086_: *mut LeanObject = *_args.add(14);
    let mut v___y_2087_: *mut LeanObject = *_args.add(15);
    let mut v___y_2088_: *mut LeanObject = *_args.add(16);
    let mut v_res_2089_: *mut LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2072_, v_keys_2073_, v_vals_2074_, v_i_2075_, v_acc_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
    lean_dec(v___y_2087_);
    lean_dec_ref(v___y_2086_);
    lean_dec(v___y_2085_);
    lean_dec_ref(v___y_2084_);
    lean_dec(v___y_2083_);
    lean_dec_ref(v___y_2082_);
    lean_dec(v___y_2081_);
    lean_dec_ref(v___y_2080_);
    lean_dec(v___y_2079_);
    lean_dec(v___y_2078_);
    lean_dec(v___y_2077_);
    lean_dec_ref(v_vals_2074_);
    lean_dec_ref(v_keys_2073_);
    return v_res_2089_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(
    mut v_f_2090_: *mut LeanObject,
    mut v_x_2091_: *mut LeanObject,
    mut v_x_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2108_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: usize = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: usize = 0;
    let mut v___x_2125_: usize = 0;
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_ks_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2091_) == 0 {
                    v_es_2105_ = lean_ctor_get(v_x_2091_, 0);
                    v_isSharedCheck_2127_ = (!lean_is_exclusive(v_x_2091_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2107_ = v_x_2091_;
                        v_isShared_2108_ = v_isSharedCheck_2127_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_2105_);
                        lean_dec(v_x_2091_);
                        v___x_2107_ = lean_box(0);
                        v_isShared_2108_ = v_isSharedCheck_2127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_2128_ = lean_ctor_get(v_x_2091_, 0);
                    lean_inc_ref(v_ks_2128_);
                    v_vs_2129_ = lean_ctor_get(v_x_2091_, 1);
                    lean_inc_ref(v_vs_2129_);
                    lean_dec_ref_known(v_x_2091_, 2);
                    v___x_2130_ = lean_unsigned_to_nat(0);
                    v___x_2131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2090_, v_ks_2128_, v_vs_2129_, v___x_2130_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                    lean_dec_ref(v_vs_2129_);
                    lean_dec_ref(v_ks_2128_);
                    return v___x_2131_;
                }
            }
            1 => {
                v___x_2109_ = lean_unsigned_to_nat(0);
                v___x_2110_ = lean_array_get_size(v_es_2105_);
                v___x_2111_ = lean_nat_dec_lt(v___x_2109_, v___x_2110_);
                if v___x_2111_ == 0 {
                    lean_dec_ref(v_es_2105_);
                    lean_dec_ref(v_f_2090_);
                    if v_isShared_2108_ == 0 {
                        lean_ctor_set_tag(v___x_2107_, 1);
                        lean_ctor_set(v___x_2107_, 0, v_x_2092_);
                        v___x_2113_ = v___x_2107_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_x_2092_);
                        v___x_2113_ = v_reuseFailAlloc_2115_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2116_ = lean_nat_dec_le(v___x_2110_, v___x_2110_);
                    if v___x_2116_ == 0 {
                        if v___x_2111_ == 0 {
                            lean_dec_ref(v_es_2105_);
                            lean_dec_ref(v_f_2090_);
                            if v_isShared_2108_ == 0 {
                                lean_ctor_set_tag(v___x_2107_, 1);
                                lean_ctor_set(v___x_2107_, 0, v_x_2092_);
                                v___x_2118_ = v___x_2107_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_x_2092_);
                                v___x_2118_ = v_reuseFailAlloc_2120_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2107_);
                            v___x_2121_ = 0usize;
                            v___x_2122_ = lean_usize_of_nat(v___x_2110_);
                            v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2090_, v_es_2105_, v___x_2121_, v___x_2122_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                            lean_dec_ref(v_es_2105_);
                            return v___x_2123_;
                        }
                    } else {
                        lean_del_object(v___x_2107_);
                        v___x_2124_ = 0usize;
                        v___x_2125_ = lean_usize_of_nat(v___x_2110_);
                        v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2090_, v_es_2105_, v___x_2124_, v___x_2125_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
                        lean_dec_ref(v_es_2105_);
                        return v___x_2126_;
                    }
                }
            }
            2 => {
                v___x_2114_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            3 => {
                v___x_2119_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2119_, 0, v___x_2118_);
                return v___x_2119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(
    mut v_f_2132_: *mut LeanObject,
    mut v_as_2133_: *mut LeanObject,
    mut v_i_2134_: usize,
    mut v_stop_2135_: usize,
    mut v_b_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v___y_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___y_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2158_ = lean_usize_dec_eq(v_i_2134_, v_stop_2135_);
                if v___x_2158_ == 0 {
                    v___x_2159_ = lean_array_uget_borrowed(v_as_2133_, v_i_2134_);
                    match lean_obj_tag(v___x_2159_) {
                        0 => {
                            v_key_2160_ = lean_ctor_get(v___x_2159_, 0);
                            v_val_2161_ = lean_ctor_get(v___x_2159_, 1);
                            lean_inc_ref(v_f_2132_);
                            lean_inc(v___y_2147_);
                            lean_inc_ref(v___y_2146_);
                            lean_inc(v___y_2145_);
                            lean_inc_ref(v___y_2144_);
                            lean_inc(v___y_2143_);
                            lean_inc_ref(v___y_2142_);
                            lean_inc(v___y_2141_);
                            lean_inc_ref(v___y_2140_);
                            lean_inc(v___y_2139_);
                            lean_inc(v___y_2138_);
                            lean_inc(v___y_2137_);
                            lean_inc(v_val_2161_);
                            lean_inc(v_key_2160_);
                            v___x_2162_ = lean_apply_15(
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
                                lean_box(0),
                            );
                            v___y_2155_ = v___x_2162_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_2163_ = lean_ctor_get(v___x_2159_, 0);
                            lean_inc(v_node_2163_);
                            lean_inc_ref(v_f_2132_);
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
                    lean_dec_ref(v_f_2132_);
                    v___x_2165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2165_, 0, v_b_2136_);
                    v___x_2166_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2166_, 0, v___x_2165_);
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
                if lean_obj_tag(v___y_2155_) == 0 {
                    v_a_2156_ = lean_ctor_get(v___y_2155_, 0);
                    if lean_obj_tag(v_a_2156_) == 0 {
                        lean_dec_ref(v_f_2132_);
                        return v___y_2155_;
                    } else {
                        lean_inc_ref(v_a_2156_);
                        lean_dec_ref_known(v___y_2155_, 1);
                        v_a_2157_ = lean_ctor_get(v_a_2156_, 0);
                        lean_inc(v_a_2157_);
                        lean_dec_ref_known(v_a_2156_, 1);
                        v_a_2150_ = v_a_2157_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_2132_);
                    return v___y_2155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_2167_: *mut LeanObject = *_args.add(0);
    let mut v_as_2168_: *mut LeanObject = *_args.add(1);
    let mut v_i_2169_: *mut LeanObject = *_args.add(2);
    let mut v_stop_2170_: *mut LeanObject = *_args.add(3);
    let mut v_b_2171_: *mut LeanObject = *_args.add(4);
    let mut v___y_2172_: *mut LeanObject = *_args.add(5);
    let mut v___y_2173_: *mut LeanObject = *_args.add(6);
    let mut v___y_2174_: *mut LeanObject = *_args.add(7);
    let mut v___y_2175_: *mut LeanObject = *_args.add(8);
    let mut v___y_2176_: *mut LeanObject = *_args.add(9);
    let mut v___y_2177_: *mut LeanObject = *_args.add(10);
    let mut v___y_2178_: *mut LeanObject = *_args.add(11);
    let mut v___y_2179_: *mut LeanObject = *_args.add(12);
    let mut v___y_2180_: *mut LeanObject = *_args.add(13);
    let mut v___y_2181_: *mut LeanObject = *_args.add(14);
    let mut v___y_2182_: *mut LeanObject = *_args.add(15);
    let mut v___y_2183_: *mut LeanObject = *_args.add(16);
    let mut v_i_boxed_2184_: usize = 0;
    let mut v_stop_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2184_ = lean_unbox_usize(v_i_2169_);
    lean_dec(v_i_2169_);
    v_stop_boxed_2185_ = lean_unbox_usize(v_stop_2170_);
    lean_dec(v_stop_2170_);
    v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2167_, v_as_2168_, v_i_boxed_2184_, v_stop_boxed_2185_, v_b_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
    lean_dec(v___y_2182_);
    lean_dec_ref(v___y_2181_);
    lean_dec(v___y_2180_);
    lean_dec_ref(v___y_2179_);
    lean_dec(v___y_2178_);
    lean_dec_ref(v___y_2177_);
    lean_dec(v___y_2176_);
    lean_dec_ref(v___y_2175_);
    lean_dec(v___y_2174_);
    lean_dec(v___y_2173_);
    lean_dec(v___y_2172_);
    lean_dec_ref(v_as_2168_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(
    mut v_f_2187_: *mut LeanObject,
    mut v_x_2188_: *mut LeanObject,
    mut v_x_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2202_: *mut LeanObject = core::ptr::null_mut();
    v_res_2202_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2187_, v_x_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
    lean_dec(v___y_2200_);
    lean_dec_ref(v___y_2199_);
    lean_dec(v___y_2198_);
    lean_dec_ref(v___y_2197_);
    lean_dec(v___y_2196_);
    lean_dec_ref(v___y_2195_);
    lean_dec(v___y_2194_);
    lean_dec_ref(v___y_2193_);
    lean_dec(v___y_2192_);
    lean_dec(v___y_2191_);
    lean_dec(v___y_2190_);
    return v_res_2202_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(
    mut v_map_2203_: *mut LeanObject,
    mut v_init_2204_: *mut LeanObject,
    mut v_f_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v_a_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_a_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2218_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                lean_closure_set(v___f_2218_, 0, v_f_2205_);
                lean_inc_ref(v_map_2203_);
                v___x_2219_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v___f_2218_, v_map_2203_, v_init_2204_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
                if lean_obj_tag(v___x_2219_) == 0 {
                    v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
                    v_isSharedCheck_2228_ = (!lean_is_exclusive(v___x_2219_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v___x_2222_ = v___x_2219_;
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2220_);
                        lean_dec(v___x_2219_);
                        v___x_2222_ = lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2229_ = lean_ctor_get(v___x_2219_, 0);
                    v_isSharedCheck_2236_ = (!lean_is_exclusive(v___x_2219_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v___x_2219_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2229_);
                        lean_dec(v___x_2219_);
                        v___x_2231_ = lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2224_ = lean_ctor_get(v_a_2220_, 0);
                lean_inc(v_a_2224_);
                lean_dec(v_a_2220_);
                if v_isShared_2223_ == 0 {
                    lean_ctor_set(v___x_2222_, 0, v_a_2224_);
                    v___x_2226_ = v___x_2222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2224_);
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
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
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
    mut v_map_2237_: *mut LeanObject,
    mut v_init_2238_: *mut LeanObject,
    mut v_f_2239_: *mut LeanObject,
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
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_2237_, v_init_2238_, v_f_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
    lean_dec(v___y_2250_);
    lean_dec_ref(v___y_2249_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    lean_dec(v___y_2246_);
    lean_dec_ref(v___y_2245_);
    lean_dec(v___y_2244_);
    lean_dec_ref(v___y_2243_);
    lean_dec(v___y_2242_);
    lean_dec(v___y_2241_);
    lean_dec(v___y_2240_);
    lean_dec_ref(v_map_2237_);
    return v_res_2252_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1()
-> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0;
    v___x_2255_ = lean_unsigned_to_nat(2);
    v___x_2256_ = lean_unsigned_to_nat(23);
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
    mut v_a_2260_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v_size_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2291_: u8 = 0;
    let mut v_a_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_a_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2272_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_,
                    v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_,
                );
                if lean_obj_tag(v___x_2272_) == 0 {
                    v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
                    lean_inc(v_a_2273_);
                    lean_dec_ref_known(v___x_2272_, 1);
                    v_vars_2274_ = lean_ctor_get(v_a_2273_, 10);
                    lean_inc_ref_n(v_vars_2274_, 2);
                    v_varMap_2275_ = lean_ctor_get(v_a_2273_, 11);
                    lean_inc_ref(v_varMap_2275_);
                    lean_dec(v_a_2273_);
                    v___f_2276_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    lean_closure_set(v___f_2276_, 0, v_vars_2274_);
                    v___x_2277_ = lean_unsigned_to_nat(0);
                    v___x_2278_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_varMap_2275_, v___x_2277_, v___f_2276_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
                    lean_dec_ref(v_varMap_2275_);
                    if lean_obj_tag(v___x_2278_) == 0 {
                        v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2291_ = (!lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2291_ == 0 {
                            v___x_2281_ = v___x_2278_;
                            v_isShared_2282_ = v_isSharedCheck_2291_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2279_);
                            lean_dec(v___x_2278_);
                            v___x_2281_ = lean_box(0);
                            v_isShared_2282_ = v_isSharedCheck_2291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_vars_2274_);
                        v_a_2292_ = lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2299_ = (!lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v___x_2294_ = v___x_2278_;
                            v_isShared_2295_ = v_isSharedCheck_2299_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2292_);
                            lean_dec(v___x_2278_);
                            v___x_2294_ = lean_box(0);
                            v_isShared_2295_ = v_isSharedCheck_2299_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2300_ = lean_ctor_get(v___x_2272_, 0);
                    v_isSharedCheck_2307_ = (!lean_is_exclusive(v___x_2272_)) as u8;
                    if v_isSharedCheck_2307_ == 0 {
                        v___x_2302_ = v___x_2272_;
                        v_isShared_2303_ = v_isSharedCheck_2307_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2300_);
                        lean_dec(v___x_2272_);
                        v___x_2302_ = lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2307_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_2283_ = lean_ctor_get(v_vars_2274_, 2);
                lean_inc(v_size_2283_);
                lean_dec_ref(v_vars_2274_);
                v___x_2284_ = lean_nat_dec_eq(v_size_2283_, v_a_2279_);
                lean_dec(v_a_2279_);
                lean_dec(v_size_2283_);
                if v___x_2284_ == 0 {
                    lean_del_object(v___x_2281_);
                    v___x_2285_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1);
                    v___x_2286_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2285_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
                    return v___x_2286_;
                } else {
                    v___x_2287_ = lean_box(0);
                    if v_isShared_2282_ == 0 {
                        lean_ctor_set(v___x_2281_, 0, v___x_2287_);
                        v___x_2289_ = v___x_2281_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
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
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
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
                    v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
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
    mut v_a_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
    mut v_a_2310_: *mut LeanObject,
    mut v_a_2311_: *mut LeanObject,
    mut v_a_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
    mut v_a_2314_: *mut LeanObject,
    mut v_a_2315_: *mut LeanObject,
    mut v_a_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_a_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2320_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(
        v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_,
        v_a_2316_, v_a_2317_, v_a_2318_,
    );
    lean_dec(v_a_2318_);
    lean_dec_ref(v_a_2317_);
    lean_dec(v_a_2316_);
    lean_dec_ref(v_a_2315_);
    lean_dec(v_a_2314_);
    lean_dec_ref(v_a_2313_);
    lean_dec(v_a_2312_);
    lean_dec_ref(v_a_2311_);
    lean_dec(v_a_2310_);
    lean_dec(v_a_2309_);
    lean_dec(v_a_2308_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(
    mut v_00_u03c3_2321_: *mut LeanObject,
    mut v_00_u03b2_2322_: *mut LeanObject,
    mut v_map_2323_: *mut LeanObject,
    mut v_init_2324_: *mut LeanObject,
    mut v_f_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_2323_, v_init_2324_, v_f_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2339_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_2340_: *mut LeanObject = *_args.add(1);
    let mut v_map_2341_: *mut LeanObject = *_args.add(2);
    let mut v_init_2342_: *mut LeanObject = *_args.add(3);
    let mut v_f_2343_: *mut LeanObject = *_args.add(4);
    let mut v___y_2344_: *mut LeanObject = *_args.add(5);
    let mut v___y_2345_: *mut LeanObject = *_args.add(6);
    let mut v___y_2346_: *mut LeanObject = *_args.add(7);
    let mut v___y_2347_: *mut LeanObject = *_args.add(8);
    let mut v___y_2348_: *mut LeanObject = *_args.add(9);
    let mut v___y_2349_: *mut LeanObject = *_args.add(10);
    let mut v___y_2350_: *mut LeanObject = *_args.add(11);
    let mut v___y_2351_: *mut LeanObject = *_args.add(12);
    let mut v___y_2352_: *mut LeanObject = *_args.add(13);
    let mut v___y_2353_: *mut LeanObject = *_args.add(14);
    let mut v___y_2354_: *mut LeanObject = *_args.add(15);
    let mut v___y_2355_: *mut LeanObject = *_args.add(16);
    let mut v_res_2356_: *mut LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(v_00_u03c3_2339_, v_00_u03b2_2340_, v_map_2341_, v_init_2342_, v_f_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
    lean_dec(v___y_2354_);
    lean_dec_ref(v___y_2353_);
    lean_dec(v___y_2352_);
    lean_dec_ref(v___y_2351_);
    lean_dec(v___y_2350_);
    lean_dec_ref(v___y_2349_);
    lean_dec(v___y_2348_);
    lean_dec_ref(v___y_2347_);
    lean_dec(v___y_2346_);
    lean_dec(v___y_2345_);
    lean_dec(v___y_2344_);
    lean_dec_ref(v_map_2341_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(
    mut v_map_2357_: *mut LeanObject,
    mut v_f_2358_: *mut LeanObject,
    mut v_init_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_2372_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2358_, v_map_2357_, v_init_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
    return v___x_2372_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(
    mut v_map_2373_: *mut LeanObject,
    mut v_f_2374_: *mut LeanObject,
    mut v_init_2375_: *mut LeanObject,
    mut v___y_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2388_: *mut LeanObject = core::ptr::null_mut();
    v_res_2388_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(v_map_2373_, v_f_2374_, v_init_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
    lean_dec(v___y_2386_);
    lean_dec_ref(v___y_2385_);
    lean_dec(v___y_2384_);
    lean_dec_ref(v___y_2383_);
    lean_dec(v___y_2382_);
    lean_dec_ref(v___y_2381_);
    lean_dec(v___y_2380_);
    lean_dec_ref(v___y_2379_);
    lean_dec(v___y_2378_);
    lean_dec(v___y_2377_);
    lean_dec(v___y_2376_);
    return v_res_2388_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(
    mut v_00_u03c3_2389_: *mut LeanObject,
    mut v_00_u03c3_2390_: *mut LeanObject,
    mut v_00_u03b2_2391_: *mut LeanObject,
    mut v_map_2392_: *mut LeanObject,
    mut v_f_2393_: *mut LeanObject,
    mut v_init_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    v___x_2407_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2393_, v_map_2392_, v_init_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    return v___x_2407_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2408_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2409_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b2_2410_: *mut LeanObject = *_args.add(2);
    let mut v_map_2411_: *mut LeanObject = *_args.add(3);
    let mut v_f_2412_: *mut LeanObject = *_args.add(4);
    let mut v_init_2413_: *mut LeanObject = *_args.add(5);
    let mut v___y_2414_: *mut LeanObject = *_args.add(6);
    let mut v___y_2415_: *mut LeanObject = *_args.add(7);
    let mut v___y_2416_: *mut LeanObject = *_args.add(8);
    let mut v___y_2417_: *mut LeanObject = *_args.add(9);
    let mut v___y_2418_: *mut LeanObject = *_args.add(10);
    let mut v___y_2419_: *mut LeanObject = *_args.add(11);
    let mut v___y_2420_: *mut LeanObject = *_args.add(12);
    let mut v___y_2421_: *mut LeanObject = *_args.add(13);
    let mut v___y_2422_: *mut LeanObject = *_args.add(14);
    let mut v___y_2423_: *mut LeanObject = *_args.add(15);
    let mut v___y_2424_: *mut LeanObject = *_args.add(16);
    let mut v___y_2425_: *mut LeanObject = *_args.add(17);
    let mut v_res_2426_: *mut LeanObject = core::ptr::null_mut();
    v_res_2426_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(v_00_u03c3_2408_, v_00_u03c3_2409_, v_00_u03b2_2410_, v_map_2411_, v_f_2412_, v_init_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
    lean_dec(v___y_2424_);
    lean_dec_ref(v___y_2423_);
    lean_dec(v___y_2422_);
    lean_dec_ref(v___y_2421_);
    lean_dec(v___y_2420_);
    lean_dec_ref(v___y_2419_);
    lean_dec(v___y_2418_);
    lean_dec_ref(v___y_2417_);
    lean_dec(v___y_2416_);
    lean_dec(v___y_2415_);
    lean_dec(v___y_2414_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(
    mut v_00_u03c3_2427_: *mut LeanObject,
    mut v_00_u03c3_2428_: *mut LeanObject,
    mut v_00_u03b1_2429_: *mut LeanObject,
    mut v_00_u03b2_2430_: *mut LeanObject,
    mut v_f_2431_: *mut LeanObject,
    mut v_x_2432_: *mut LeanObject,
    mut v_x_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
    mut v___y_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2431_, v_x_2432_, v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
    return v___x_2446_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2447_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2448_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_2449_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_2450_: *mut LeanObject = *_args.add(3);
    let mut v_f_2451_: *mut LeanObject = *_args.add(4);
    let mut v_x_2452_: *mut LeanObject = *_args.add(5);
    let mut v_x_2453_: *mut LeanObject = *_args.add(6);
    let mut v___y_2454_: *mut LeanObject = *_args.add(7);
    let mut v___y_2455_: *mut LeanObject = *_args.add(8);
    let mut v___y_2456_: *mut LeanObject = *_args.add(9);
    let mut v___y_2457_: *mut LeanObject = *_args.add(10);
    let mut v___y_2458_: *mut LeanObject = *_args.add(11);
    let mut v___y_2459_: *mut LeanObject = *_args.add(12);
    let mut v___y_2460_: *mut LeanObject = *_args.add(13);
    let mut v___y_2461_: *mut LeanObject = *_args.add(14);
    let mut v___y_2462_: *mut LeanObject = *_args.add(15);
    let mut v___y_2463_: *mut LeanObject = *_args.add(16);
    let mut v___y_2464_: *mut LeanObject = *_args.add(17);
    let mut v___y_2465_: *mut LeanObject = *_args.add(18);
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_2447_, v_00_u03c3_2448_, v_00_u03b1_2449_, v_00_u03b2_2450_, v_f_2451_, v_x_2452_, v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
    lean_dec(v___y_2464_);
    lean_dec_ref(v___y_2463_);
    lean_dec(v___y_2462_);
    lean_dec_ref(v___y_2461_);
    lean_dec(v___y_2460_);
    lean_dec_ref(v___y_2459_);
    lean_dec(v___y_2458_);
    lean_dec_ref(v___y_2457_);
    lean_dec(v___y_2456_);
    lean_dec(v___y_2455_);
    lean_dec(v___y_2454_);
    return v_res_2466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(
    mut v_00_u03b1_2467_: *mut LeanObject,
    mut v_00_u03b2_2468_: *mut LeanObject,
    mut v_00_u03c3_2469_: *mut LeanObject,
    mut v_00_u03c3_2470_: *mut LeanObject,
    mut v_f_2471_: *mut LeanObject,
    mut v_as_2472_: *mut LeanObject,
    mut v_i_2473_: usize,
    mut v_stop_2474_: usize,
    mut v_b_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2471_, v_as_2472_, v_i_2473_, v_stop_2474_, v_b_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
    return v___x_2488_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_2489_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_2490_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3_2491_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03c3_2492_: *mut LeanObject = *_args.add(3);
    let mut v_f_2493_: *mut LeanObject = *_args.add(4);
    let mut v_as_2494_: *mut LeanObject = *_args.add(5);
    let mut v_i_2495_: *mut LeanObject = *_args.add(6);
    let mut v_stop_2496_: *mut LeanObject = *_args.add(7);
    let mut v_b_2497_: *mut LeanObject = *_args.add(8);
    let mut v___y_2498_: *mut LeanObject = *_args.add(9);
    let mut v___y_2499_: *mut LeanObject = *_args.add(10);
    let mut v___y_2500_: *mut LeanObject = *_args.add(11);
    let mut v___y_2501_: *mut LeanObject = *_args.add(12);
    let mut v___y_2502_: *mut LeanObject = *_args.add(13);
    let mut v___y_2503_: *mut LeanObject = *_args.add(14);
    let mut v___y_2504_: *mut LeanObject = *_args.add(15);
    let mut v___y_2505_: *mut LeanObject = *_args.add(16);
    let mut v___y_2506_: *mut LeanObject = *_args.add(17);
    let mut v___y_2507_: *mut LeanObject = *_args.add(18);
    let mut v___y_2508_: *mut LeanObject = *_args.add(19);
    let mut v___y_2509_: *mut LeanObject = *_args.add(20);
    let mut v_i_boxed_2510_: usize = 0;
    let mut v_stop_boxed_2511_: usize = 0;
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2510_ = lean_unbox_usize(v_i_2495_);
    lean_dec(v_i_2495_);
    v_stop_boxed_2511_ = lean_unbox_usize(v_stop_2496_);
    lean_dec(v_stop_2496_);
    v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_2489_, v_00_u03b2_2490_, v_00_u03c3_2491_, v_00_u03c3_2492_, v_f_2493_, v_as_2494_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
    lean_dec(v___y_2508_);
    lean_dec_ref(v___y_2507_);
    lean_dec(v___y_2506_);
    lean_dec_ref(v___y_2505_);
    lean_dec(v___y_2504_);
    lean_dec_ref(v___y_2503_);
    lean_dec(v___y_2502_);
    lean_dec_ref(v___y_2501_);
    lean_dec(v___y_2500_);
    lean_dec(v___y_2499_);
    lean_dec(v___y_2498_);
    lean_dec_ref(v_as_2494_);
    return v_res_2512_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(
    mut v_00_u03c3_2513_: *mut LeanObject,
    mut v_00_u03c3_2514_: *mut LeanObject,
    mut v_00_u03b1_2515_: *mut LeanObject,
    mut v_00_u03b2_2516_: *mut LeanObject,
    mut v_f_2517_: *mut LeanObject,
    mut v_keys_2518_: *mut LeanObject,
    mut v_vals_2519_: *mut LeanObject,
    mut v_heq_2520_: *mut LeanObject,
    mut v_i_2521_: *mut LeanObject,
    mut v_acc_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___x_2535_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2517_, v_keys_2518_, v_vals_2519_, v_i_2521_, v_acc_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
    return v___x_2535_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2536_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2537_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_2538_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_2539_: *mut LeanObject = *_args.add(3);
    let mut v_f_2540_: *mut LeanObject = *_args.add(4);
    let mut v_keys_2541_: *mut LeanObject = *_args.add(5);
    let mut v_vals_2542_: *mut LeanObject = *_args.add(6);
    let mut v_heq_2543_: *mut LeanObject = *_args.add(7);
    let mut v_i_2544_: *mut LeanObject = *_args.add(8);
    let mut v_acc_2545_: *mut LeanObject = *_args.add(9);
    let mut v___y_2546_: *mut LeanObject = *_args.add(10);
    let mut v___y_2547_: *mut LeanObject = *_args.add(11);
    let mut v___y_2548_: *mut LeanObject = *_args.add(12);
    let mut v___y_2549_: *mut LeanObject = *_args.add(13);
    let mut v___y_2550_: *mut LeanObject = *_args.add(14);
    let mut v___y_2551_: *mut LeanObject = *_args.add(15);
    let mut v___y_2552_: *mut LeanObject = *_args.add(16);
    let mut v___y_2553_: *mut LeanObject = *_args.add(17);
    let mut v___y_2554_: *mut LeanObject = *_args.add(18);
    let mut v___y_2555_: *mut LeanObject = *_args.add(19);
    let mut v___y_2556_: *mut LeanObject = *_args.add(20);
    let mut v___y_2557_: *mut LeanObject = *_args.add(21);
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_2536_, v_00_u03c3_2537_, v_00_u03b1_2538_, v_00_u03b2_2539_, v_f_2540_, v_keys_2541_, v_vals_2542_, v_heq_2543_, v_i_2544_, v_acc_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
    lean_dec(v___y_2556_);
    lean_dec_ref(v___y_2555_);
    lean_dec(v___y_2554_);
    lean_dec_ref(v___y_2553_);
    lean_dec(v___y_2552_);
    lean_dec_ref(v___y_2551_);
    lean_dec(v___y_2550_);
    lean_dec_ref(v___y_2549_);
    lean_dec(v___y_2548_);
    lean_dec(v___y_2547_);
    lean_dec(v___y_2546_);
    lean_dec_ref(v_vals_2542_);
    lean_dec_ref(v_keys_2541_);
    return v_res_2558_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2()
-> *mut LeanObject {
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    v___x_2561_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1;
    v___x_2562_ = lean_unsigned_to_nat(6);
    v___x_2563_ = lean_unsigned_to_nat(36);
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
-> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4;
    v___x_2571_ = lean_unsigned_to_nat(6);
    v___x_2572_ = lean_unsigned_to_nat(34);
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
-> *mut LeanObject {
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    v___x_2577_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6;
    v___x_2578_ = lean_unsigned_to_nat(4);
    v___x_2579_ = lean_unsigned_to_nat(31);
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
    mut v_s_2583_: *mut LeanObject,
    mut v_simplified_2584_: u8,
    mut v_a_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___y_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: u8 = 0;
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2677_: u8 = 0;
    let mut v_a_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2635_ = l_Lean_Meta_Grind_AC_isCommutative(
                    v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_,
                    v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_,
                );
                if lean_obj_tag(v___x_2635_) == 0 {
                    v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2677_ = (!lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2677_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2677_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2636_);
                        lean_dec(v___x_2635_);
                        v___x_2638_ = lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2677_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2678_ = lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2685_ = (!lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v___x_2680_ = v___x_2635_;
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2678_);
                        lean_dec(v___x_2635_);
                        v___x_2680_ = lean_box(0);
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
                if lean_obj_tag(v___x_2609_) == 0 {
                    v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2626_ = (!lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2626_ == 0 {
                        v___x_2612_ = v___x_2609_;
                        v_isShared_2613_ = v_isSharedCheck_2626_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2610_);
                        lean_dec(v___x_2609_);
                        v___x_2612_ = lean_box(0);
                        v_isShared_2613_ = v_isSharedCheck_2626_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2627_ = lean_ctor_get(v___x_2609_, 0);
                    v_isSharedCheck_2634_ = (!lean_is_exclusive(v___x_2609_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2609_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2627_);
                        lean_dec(v___x_2609_);
                        v___x_2629_ = lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2614_ = (lean_unbox(v_a_2610_) as u8);
                lean_dec(v_a_2610_);
                if v___x_2614_ == 0 {
                    v___x_2615_ = lean_box(0);
                    if v_isShared_2613_ == 0 {
                        lean_ctor_set(v___x_2612_, 0, v___x_2615_);
                        v___x_2617_ = v___x_2612_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
                        v___x_2617_ = v_reuseFailAlloc_2618_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2619_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_2583_);
                    if v___x_2619_ == 0 {
                        lean_del_object(v___x_2612_);
                        v___x_2620_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2);
                        v___x_2621_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_2620_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
                        return v___x_2621_;
                    } else {
                        v___x_2622_ = lean_box(0);
                        if v_isShared_2613_ == 0 {
                            lean_ctor_set(v___x_2612_, 0, v___x_2622_);
                            v___x_2624_ = v___x_2612_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
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
                    v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2632_;
            }
            7 => {
                v___x_2673_ = (lean_unbox(v_a_2636_) as u8);
                lean_dec(v_a_2636_);
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
                        lean_del_object(v___x_2638_);
                        v___x_2675_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7);
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
                    v___x_2652_ = lean_box(0);
                    if v_isShared_2639_ == 0 {
                        lean_ctor_set(v___x_2638_, 0, v___x_2652_);
                        v___x_2654_ = v___x_2638_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
                        v___x_2654_ = v_reuseFailAlloc_2655_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2638_);
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
                    if lean_obj_tag(v___x_2656_) == 0 {
                        v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                        lean_inc(v_a_2657_);
                        lean_dec_ref_known(v___x_2656_, 1);
                        v___x_2658_ = (lean_unbox(v_a_2657_) as u8);
                        lean_dec(v_a_2657_);
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
                            v___x_2659_ = lean_unsigned_to_nat(0);
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
                                    v___x_2663_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5);
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
                        v_a_2665_ = lean_ctor_get(v___x_2656_, 0);
                        v_isSharedCheck_2672_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                        if v_isSharedCheck_2672_ == 0 {
                            v___x_2667_ = v___x_2656_;
                            v_isShared_2668_ = v_isSharedCheck_2672_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2665_);
                            lean_dec(v___x_2656_);
                            v___x_2667_ = lean_box(0);
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
                    v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
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
                    v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
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
    mut v_s_2686_: *mut LeanObject,
    mut v_simplified_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplified_boxed_2700_: u8 = 0;
    let mut v_res_2701_: *mut LeanObject = core::ptr::null_mut();
    v_simplified_boxed_2700_ = (lean_unbox(v_simplified_2687_) as u8);
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
    lean_dec(v_a_2698_);
    lean_dec_ref(v_a_2697_);
    lean_dec(v_a_2696_);
    lean_dec_ref(v_a_2695_);
    lean_dec(v_a_2694_);
    lean_dec_ref(v_a_2693_);
    lean_dec(v_a_2692_);
    lean_dec_ref(v_a_2691_);
    lean_dec(v_a_2690_);
    lean_dec(v_a_2689_);
    lean_dec(v_a_2688_);
    lean_dec_ref(v_s_2686_);
    return v_res_2701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(
    mut v_lhs_2702_: *mut LeanObject,
    mut v_rhs_2703_: *mut LeanObject,
    mut v_simplified_2704_: u8,
    mut v_a_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
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
    if lean_obj_tag(v___x_2717_) == 0 {
        let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2717_, 1);
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
    mut v_lhs_2719_: *mut LeanObject,
    mut v_rhs_2720_: *mut LeanObject,
    mut v_simplified_2721_: *mut LeanObject,
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
    mut v_a_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplified_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_simplified_boxed_2734_ = (lean_unbox(v_simplified_2721_) as u8);
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
    lean_dec(v_a_2732_);
    lean_dec_ref(v_a_2731_);
    lean_dec(v_a_2730_);
    lean_dec_ref(v_a_2729_);
    lean_dec(v_a_2728_);
    lean_dec_ref(v_a_2727_);
    lean_dec(v_a_2726_);
    lean_dec_ref(v_a_2725_);
    lean_dec(v_a_2724_);
    lean_dec(v_a_2723_);
    lean_dec(v_a_2722_);
    lean_dec_ref(v_rhs_2720_);
    lean_dec_ref(v_lhs_2719_);
    return v_res_2735_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_2736_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(
    mut v_msg_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765__overap_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2750_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0);
    v___f_2751_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2751_, 0, v___x_2750_);
    v___x_3765__overap_2752_ = lean_panic_fn_borrowed(v___f_2751_, v_msg_2737_);
    lean_dec_ref(v___f_2751_);
    lean_inc(v___y_2748_);
    lean_inc_ref(v___y_2747_);
    lean_inc(v___y_2746_);
    lean_inc_ref(v___y_2745_);
    lean_inc(v___y_2744_);
    lean_inc_ref(v___y_2743_);
    lean_inc(v___y_2742_);
    lean_inc_ref(v___y_2741_);
    lean_inc(v___y_2740_);
    lean_inc(v___y_2739_);
    lean_inc(v___y_2738_);
    v___x_2753_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_2753_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(
    mut v_msg_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2767_: *mut LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
    lean_dec(v___y_2765_);
    lean_dec_ref(v___y_2764_);
    lean_dec(v___y_2763_);
    lean_dec_ref(v___y_2762_);
    lean_dec(v___y_2761_);
    lean_dec_ref(v___y_2760_);
    lean_dec(v___y_2759_);
    lean_dec_ref(v___y_2758_);
    lean_dec(v___y_2757_);
    lean_dec(v___y_2756_);
    lean_dec(v___y_2755_);
    return v_res_2767_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1;
    v___x_2771_ = lean_unsigned_to_nat(4);
    v___x_2772_ = lean_unsigned_to_nat(43);
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
    mut v_as_x27_2776_: *mut LeanObject,
    mut v_b_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
    mut v___y_2780_: *mut LeanObject,
    mut v___y_2781_: *mut LeanObject,
    mut v___y_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v_a_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2776_) == 0 {
                    v___x_2790_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2790_, 0, v_b_2777_);
                    return v___x_2790_;
                } else {
                    v_head_2791_ = lean_ctor_get(v_as_x27_2776_, 0);
                    v_tail_2792_ = lean_ctor_get(v_as_x27_2776_, 1);
                    v_lhs_2793_ = lean_ctor_get(v_head_2791_, 0);
                    v_rhs_2794_ = lean_ctor_get(v_head_2791_, 1);
                    v___x_2795_ = l_Lean_Grind_AC_Seq_compare(v_lhs_2793_, v_rhs_2794_);
                    v___x_2796_ = 2;
                    v___x_2797_ = l_instDecidableEqOrdering(v___x_2795_, v___x_2796_);
                    if v___x_2797_ == 0 {
                        v___x_2798_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2);
                        v___x_2799_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v___x_2798_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
                        if lean_obj_tag(v___x_2799_) == 0 {
                            v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
                            v_isSharedCheck_2810_ = (!lean_is_exclusive(v___x_2799_)) as u8;
                            if v_isSharedCheck_2810_ == 0 {
                                v___x_2802_ = v___x_2799_;
                                v_isShared_2803_ = v_isSharedCheck_2810_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2800_);
                                lean_dec(v___x_2799_);
                                v___x_2802_ = lean_box(0);
                                v_isShared_2803_ = v_isSharedCheck_2810_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2811_ = lean_ctor_get(v___x_2799_, 0);
                            v_isSharedCheck_2818_ = (!lean_is_exclusive(v___x_2799_)) as u8;
                            if v_isSharedCheck_2818_ == 0 {
                                v___x_2813_ = v___x_2799_;
                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2811_);
                                lean_dec(v___x_2799_);
                                v___x_2813_ = lean_box(0);
                                v_isShared_2814_ = v_isSharedCheck_2818_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2819_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_2793_, v_rhs_2794_, v___x_2797_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
                        if lean_obj_tag(v___x_2819_) == 0 {
                            lean_dec_ref_known(v___x_2819_, 1);
                            v___x_2820_ = lean_box(0);
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
                if lean_obj_tag(v_a_2800_) == 0 {
                    v_a_2804_ = lean_ctor_get(v_a_2800_, 0);
                    lean_inc(v_a_2804_);
                    lean_dec_ref_known(v_a_2800_, 1);
                    if v_isShared_2803_ == 0 {
                        lean_ctor_set(v___x_2802_, 0, v_a_2804_);
                        v___x_2806_ = v___x_2802_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2804_);
                        v___x_2806_ = v_reuseFailAlloc_2807_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2802_);
                    v_a_2808_ = lean_ctor_get(v_a_2800_, 0);
                    lean_inc(v_a_2808_);
                    lean_dec_ref_known(v_a_2800_, 1);
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
                    v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
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
    mut v_as_x27_2822_: *mut LeanObject,
    mut v_b_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2836_: *mut LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_2822_, v_b_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
    lean_dec(v___y_2834_);
    lean_dec_ref(v___y_2833_);
    lean_dec(v___y_2832_);
    lean_dec_ref(v___y_2831_);
    lean_dec(v___y_2830_);
    lean_dec_ref(v___y_2829_);
    lean_dec(v___y_2828_);
    lean_dec_ref(v___y_2827_);
    lean_dec(v___y_2826_);
    lean_dec(v___y_2825_);
    lean_dec(v___y_2824_);
    lean_dec(v_as_x27_2822_);
    return v_res_2836_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_a_2839_: *mut LeanObject,
    mut v_a_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_unused_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2849_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_,
                    v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_,
                );
                if lean_obj_tag(v___x_2849_) == 0 {
                    v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
                    lean_inc(v_a_2850_);
                    lean_dec_ref_known(v___x_2849_, 1);
                    v_basis_2851_ = lean_ctor_get(v_a_2850_, 15);
                    lean_inc(v_basis_2851_);
                    lean_dec(v_a_2850_);
                    v___x_2852_ = lean_box(0);
                    v___x_2853_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_basis_2851_, v___x_2852_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
                    lean_dec(v_basis_2851_);
                    if lean_obj_tag(v___x_2853_) == 0 {
                        v_isSharedCheck_2860_ = (!lean_is_exclusive(v___x_2853_)) as u8;
                        if v_isSharedCheck_2860_ == 0 {
                            v_unused_2861_ = lean_ctor_get(v___x_2853_, 0);
                            lean_dec(v_unused_2861_);
                            v___x_2855_ = v___x_2853_;
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2853_);
                            v___x_2855_ = lean_box(0);
                            v_isShared_2856_ = v_isSharedCheck_2860_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2853_;
                    }
                } else {
                    v_a_2862_ = lean_ctor_get(v___x_2849_, 0);
                    v_isSharedCheck_2869_ = (!lean_is_exclusive(v___x_2849_)) as u8;
                    if v_isSharedCheck_2869_ == 0 {
                        v___x_2864_ = v___x_2849_;
                        v_isShared_2865_ = v_isSharedCheck_2869_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2862_);
                        lean_dec(v___x_2849_);
                        v___x_2864_ = lean_box(0);
                        v_isShared_2865_ = v_isSharedCheck_2869_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2856_ == 0 {
                    lean_ctor_set(v___x_2855_, 0, v___x_2852_);
                    v___x_2858_ = v___x_2855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2852_);
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
                    v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
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
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v_a_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2882_: *mut LeanObject = core::ptr::null_mut();
    v_res_2882_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
        v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_,
        v_a_2878_, v_a_2879_, v_a_2880_,
    );
    lean_dec(v_a_2880_);
    lean_dec_ref(v_a_2879_);
    lean_dec(v_a_2878_);
    lean_dec_ref(v_a_2877_);
    lean_dec(v_a_2876_);
    lean_dec_ref(v_a_2875_);
    lean_dec(v_a_2874_);
    lean_dec_ref(v_a_2873_);
    lean_dec(v_a_2872_);
    lean_dec(v_a_2871_);
    lean_dec(v_a_2870_);
    return v_res_2882_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(
    mut v_as_2883_: *mut LeanObject,
    mut v_as_x27_2884_: *mut LeanObject,
    mut v_b_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
    mut v___y_2889_: *mut LeanObject,
    mut v___y_2890_: *mut LeanObject,
    mut v___y_2891_: *mut LeanObject,
    mut v___y_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    v___x_2899_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_2884_, v_b_2885_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
    return v___x_2899_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(
    mut v_as_2900_: *mut LeanObject,
    mut v_as_x27_2901_: *mut LeanObject,
    mut v_b_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
    mut v___y_2908_: *mut LeanObject,
    mut v___y_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2916_: *mut LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(v_as_2900_, v_as_x27_2901_, v_b_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
    lean_dec(v___y_2914_);
    lean_dec_ref(v___y_2913_);
    lean_dec(v___y_2912_);
    lean_dec_ref(v___y_2911_);
    lean_dec(v___y_2910_);
    lean_dec_ref(v___y_2909_);
    lean_dec(v___y_2908_);
    lean_dec_ref(v___y_2907_);
    lean_dec(v___y_2906_);
    lean_dec(v___y_2905_);
    lean_dec(v___y_2904_);
    lean_dec(v_as_x27_2901_);
    lean_dec(v_as_2900_);
    return v_res_2916_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(
    mut v_init_2917_: *mut LeanObject,
    mut v_x_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
    mut v___y_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2918_) == 0 {
                    v_k_2931_ = lean_ctor_get(v_x_2918_, 1);
                    v_l_2932_ = lean_ctor_get(v_x_2918_, 3);
                    v_r_2933_ = lean_ctor_get(v_x_2918_, 4);
                    v___x_2934_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_2917_, v_l_2932_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                    if lean_obj_tag(v___x_2934_) == 0 {
                        lean_dec_ref_known(v___x_2934_, 1);
                        v_lhs_2935_ = lean_ctor_get(v_k_2931_, 0);
                        v_rhs_2936_ = lean_ctor_get(v_k_2931_, 1);
                        v___x_2937_ = 0;
                        v___x_2938_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_2935_, v_rhs_2936_, v___x_2937_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
                        if lean_obj_tag(v___x_2938_) == 0 {
                            lean_dec_ref_known(v___x_2938_, 1);
                            v___x_2939_ = lean_box(0);
                            v_init_2917_ = v___x_2939_;
                            v_x_2918_ = v_r_2933_;
                            state = 0;
                            continue;
                        } else {
                            v_a_2941_ = lean_ctor_get(v___x_2938_, 0);
                            v_isSharedCheck_2948_ = (!lean_is_exclusive(v___x_2938_)) as u8;
                            if v_isSharedCheck_2948_ == 0 {
                                v___x_2943_ = v___x_2938_;
                                v_isShared_2944_ = v_isSharedCheck_2948_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2941_);
                                lean_dec(v___x_2938_);
                                v___x_2943_ = lean_box(0);
                                v_isShared_2944_ = v_isSharedCheck_2948_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2934_;
                    }
                } else {
                    v___x_2949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2949_, 0, v_init_2917_);
                    v___x_2950_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2950_, 0, v___x_2949_);
                    return v___x_2950_;
                }
            }
            1 => {
                if v_isShared_2944_ == 0 {
                    v___x_2946_ = v___x_2943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
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
    mut v_init_2951_: *mut LeanObject,
    mut v_x_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
    mut v___y_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_2951_, v_x_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
    lean_dec(v___y_2963_);
    lean_dec_ref(v___y_2962_);
    lean_dec(v___y_2961_);
    lean_dec_ref(v___y_2960_);
    lean_dec(v___y_2959_);
    lean_dec_ref(v___y_2958_);
    lean_dec(v___y_2957_);
    lean_dec_ref(v___y_2956_);
    lean_dec(v___y_2955_);
    lean_dec(v___y_2954_);
    lean_dec(v___y_2953_);
    lean_dec(v_x_2952_);
    return v_res_2965_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
    mut v_a_2975_: *mut LeanObject,
    mut v_a_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_a_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_,
                    v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_,
                );
                if lean_obj_tag(v___x_2978_) == 0 {
                    v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
                    lean_inc(v_a_2979_);
                    lean_dec_ref_known(v___x_2978_, 1);
                    v_queue_2980_ = lean_ctor_get(v_a_2979_, 14);
                    lean_inc(v_queue_2980_);
                    lean_dec(v_a_2979_);
                    v___x_2981_ = lean_box(0);
                    v___x_2982_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v___x_2981_, v_queue_2980_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
                    lean_dec(v_queue_2980_);
                    if lean_obj_tag(v___x_2982_) == 0 {
                        v_isSharedCheck_2989_ = (!lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_2989_ == 0 {
                            v_unused_2990_ = lean_ctor_get(v___x_2982_, 0);
                            lean_dec(v_unused_2990_);
                            v___x_2984_ = v___x_2982_;
                            v_isShared_2985_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2982_);
                            v___x_2984_ = lean_box(0);
                            v_isShared_2985_ = v_isSharedCheck_2989_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2991_ = lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_2998_ = (!lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_2998_ == 0 {
                            v___x_2993_ = v___x_2982_;
                            v_isShared_2994_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2991_);
                            lean_dec(v___x_2982_);
                            v___x_2993_ = lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_2998_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2999_ = lean_ctor_get(v___x_2978_, 0);
                    v_isSharedCheck_3006_ = (!lean_is_exclusive(v___x_2978_)) as u8;
                    if v_isSharedCheck_3006_ == 0 {
                        v___x_3001_ = v___x_2978_;
                        v_isShared_3002_ = v_isSharedCheck_3006_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2999_);
                        lean_dec(v___x_2978_);
                        v___x_3001_ = lean_box(0);
                        v_isShared_3002_ = v_isSharedCheck_3006_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2985_ == 0 {
                    lean_ctor_set(v___x_2984_, 0, v___x_2981_);
                    v___x_2987_ = v___x_2984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2981_);
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
                    v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
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
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
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
    mut v_a_3007_: *mut LeanObject,
    mut v_a_3008_: *mut LeanObject,
    mut v_a_3009_: *mut LeanObject,
    mut v_a_3010_: *mut LeanObject,
    mut v_a_3011_: *mut LeanObject,
    mut v_a_3012_: *mut LeanObject,
    mut v_a_3013_: *mut LeanObject,
    mut v_a_3014_: *mut LeanObject,
    mut v_a_3015_: *mut LeanObject,
    mut v_a_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3019_: *mut LeanObject = core::ptr::null_mut();
    v_res_3019_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
        v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_,
        v_a_3015_, v_a_3016_, v_a_3017_,
    );
    lean_dec(v_a_3017_);
    lean_dec_ref(v_a_3016_);
    lean_dec(v_a_3015_);
    lean_dec_ref(v_a_3014_);
    lean_dec(v_a_3013_);
    lean_dec_ref(v_a_3012_);
    lean_dec(v_a_3011_);
    lean_dec_ref(v_a_3010_);
    lean_dec(v_a_3009_);
    lean_dec(v_a_3008_);
    lean_dec(v_a_3007_);
    return v_res_3019_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(
    mut v_as_3023_: *mut LeanObject,
    mut v_sz_3024_: usize,
    mut v_i_3025_: usize,
    mut v_b_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: usize = 0;
    let mut v___x_3047_: usize = 0;
    let mut v_a_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3039_ = lean_usize_dec_lt(v_i_3025_, v_sz_3024_);
                if v___x_3039_ == 0 {
                    v___x_3040_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3040_, 0, v_b_3026_);
                    return v___x_3040_;
                } else {
                    lean_dec_ref(v_b_3026_);
                    v_a_3041_ = lean_array_uget_borrowed(v_as_3023_, v_i_3025_);
                    v_lhs_3042_ = lean_ctor_get(v_a_3041_, 0);
                    v_rhs_3043_ = lean_ctor_get(v_a_3041_, 1);
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
                    if lean_obj_tag(v___x_3044_) == 0 {
                        lean_dec_ref_known(v___x_3044_, 1);
                        v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3046_ = 1usize;
                        v___x_3047_ = lean_usize_add(v_i_3025_, v___x_3046_);
                        v_i_3025_ = v___x_3047_;
                        v_b_3026_ = v___x_3045_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3049_ = lean_ctor_get(v___x_3044_, 0);
                        v_isSharedCheck_3056_ = (!lean_is_exclusive(v___x_3044_)) as u8;
                        if v_isSharedCheck_3056_ == 0 {
                            v___x_3051_ = v___x_3044_;
                            v_isShared_3052_ = v_isSharedCheck_3056_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3049_);
                            lean_dec(v___x_3044_);
                            v___x_3051_ = lean_box(0);
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
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
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
    mut v_as_3057_: *mut LeanObject,
    mut v_sz_3058_: *mut LeanObject,
    mut v_i_3059_: *mut LeanObject,
    mut v_b_3060_: *mut LeanObject,
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
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3073_: usize = 0;
    let mut v_i_boxed_3074_: usize = 0;
    let mut v_res_3075_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3073_ = lean_unbox_usize(v_sz_3058_);
    lean_dec(v_sz_3058_);
    v_i_boxed_3074_ = lean_unbox_usize(v_i_3059_);
    lean_dec(v_i_3059_);
    v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_3057_, v_sz_boxed_3073_, v_i_boxed_3074_, v_b_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
    lean_dec(v___y_3071_);
    lean_dec_ref(v___y_3070_);
    lean_dec(v___y_3069_);
    lean_dec_ref(v___y_3068_);
    lean_dec(v___y_3067_);
    lean_dec_ref(v___y_3066_);
    lean_dec(v___y_3065_);
    lean_dec_ref(v___y_3064_);
    lean_dec(v___y_3063_);
    lean_dec(v___y_3062_);
    lean_dec(v___y_3061_);
    lean_dec_ref(v_as_3057_);
    return v_res_3075_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(
    mut v_as_3076_: *mut LeanObject,
    mut v_sz_3077_: usize,
    mut v_i_3078_: usize,
    mut v_b_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
    mut v___y_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: usize = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_usize_dec_lt(v_i_3078_, v_sz_3077_);
                if v___x_3092_ == 0 {
                    v___x_3093_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3093_, 0, v_b_3079_);
                    return v___x_3093_;
                } else {
                    lean_dec_ref(v_b_3079_);
                    v_a_3094_ = lean_array_uget_borrowed(v_as_3076_, v_i_3078_);
                    v_lhs_3095_ = lean_ctor_get(v_a_3094_, 0);
                    v_rhs_3096_ = lean_ctor_get(v_a_3094_, 1);
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
                    if lean_obj_tag(v___x_3097_) == 0 {
                        lean_dec_ref_known(v___x_3097_, 1);
                        v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3099_ = 1usize;
                        v___x_3100_ = lean_usize_add(v_i_3078_, v___x_3099_);
                        v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_3076_, v_sz_3077_, v___x_3100_, v___x_3098_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
                        return v___x_3101_;
                    } else {
                        v_a_3102_ = lean_ctor_get(v___x_3097_, 0);
                        v_isSharedCheck_3109_ = (!lean_is_exclusive(v___x_3097_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v___x_3104_ = v___x_3097_;
                            v_isShared_3105_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3102_);
                            lean_dec(v___x_3097_);
                            v___x_3104_ = lean_box(0);
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
                    v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
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
    mut v_as_3110_: *mut LeanObject,
    mut v_sz_3111_: *mut LeanObject,
    mut v_i_3112_: *mut LeanObject,
    mut v_b_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3126_: usize = 0;
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_res_3128_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3126_ = lean_unbox_usize(v_sz_3111_);
    lean_dec(v_sz_3111_);
    v_i_boxed_3127_ = lean_unbox_usize(v_i_3112_);
    lean_dec(v_i_3112_);
    v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_as_3110_, v_sz_boxed_3126_, v_i_boxed_3127_, v_b_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
    lean_dec(v___y_3124_);
    lean_dec_ref(v___y_3123_);
    lean_dec(v___y_3122_);
    lean_dec_ref(v___y_3121_);
    lean_dec(v___y_3120_);
    lean_dec_ref(v___y_3119_);
    lean_dec(v___y_3118_);
    lean_dec_ref(v___y_3117_);
    lean_dec(v___y_3116_);
    lean_dec(v___y_3115_);
    lean_dec(v___y_3114_);
    lean_dec_ref(v_as_3110_);
    return v_res_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(
    mut v_as_3132_: *mut LeanObject,
    mut v_sz_3133_: usize,
    mut v_i_3134_: usize,
    mut v_b_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: usize = 0;
    let mut v___x_3156_: usize = 0;
    let mut v_a_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3161_: u8 = 0;
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3148_ = lean_usize_dec_lt(v_i_3134_, v_sz_3133_);
                if v___x_3148_ == 0 {
                    v___x_3149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3149_, 0, v_b_3135_);
                    return v___x_3149_;
                } else {
                    lean_dec_ref(v_b_3135_);
                    v_a_3150_ = lean_array_uget_borrowed(v_as_3132_, v_i_3134_);
                    v_lhs_3151_ = lean_ctor_get(v_a_3150_, 0);
                    v_rhs_3152_ = lean_ctor_get(v_a_3150_, 1);
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
                    if lean_obj_tag(v___x_3153_) == 0 {
                        lean_dec_ref_known(v___x_3153_, 1);
                        v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_3155_ = 1usize;
                        v___x_3156_ = lean_usize_add(v_i_3134_, v___x_3155_);
                        v_i_3134_ = v___x_3156_;
                        v_b_3135_ = v___x_3154_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3158_ = lean_ctor_get(v___x_3153_, 0);
                        v_isSharedCheck_3165_ = (!lean_is_exclusive(v___x_3153_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3160_ = v___x_3153_;
                            v_isShared_3161_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3158_);
                            lean_dec(v___x_3153_);
                            v___x_3160_ = lean_box(0);
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
                    v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
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
    mut v_as_3166_: *mut LeanObject,
    mut v_sz_3167_: *mut LeanObject,
    mut v_i_3168_: *mut LeanObject,
    mut v_b_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3182_: usize = 0;
    let mut v_i_boxed_3183_: usize = 0;
    let mut v_res_3184_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3182_ = lean_unbox_usize(v_sz_3167_);
    lean_dec(v_sz_3167_);
    v_i_boxed_3183_ = lean_unbox_usize(v_i_3168_);
    lean_dec(v_i_3168_);
    v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_3166_, v_sz_boxed_3182_, v_i_boxed_3183_, v_b_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
    lean_dec(v___y_3180_);
    lean_dec_ref(v___y_3179_);
    lean_dec(v___y_3178_);
    lean_dec_ref(v___y_3177_);
    lean_dec(v___y_3176_);
    lean_dec_ref(v___y_3175_);
    lean_dec(v___y_3174_);
    lean_dec_ref(v___y_3173_);
    lean_dec(v___y_3172_);
    lean_dec(v___y_3171_);
    lean_dec(v___y_3170_);
    lean_dec_ref(v_as_3166_);
    return v_res_3184_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(
    mut v_as_3185_: *mut LeanObject,
    mut v_sz_3186_: usize,
    mut v_i_3187_: usize,
    mut v_b_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
    mut v___y_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_3201_ = lean_usize_dec_lt(v_i_3187_, v_sz_3186_);
                if v___x_3201_ == 0 {
                    v___x_3202_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3202_, 0, v_b_3188_);
                    return v___x_3202_;
                } else {
                    lean_dec_ref(v_b_3188_);
                    v_a_3203_ = lean_array_uget_borrowed(v_as_3185_, v_i_3187_);
                    v_lhs_3204_ = lean_ctor_get(v_a_3203_, 0);
                    v_rhs_3205_ = lean_ctor_get(v_a_3203_, 1);
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
                    if lean_obj_tag(v___x_3206_) == 0 {
                        lean_dec_ref_known(v___x_3206_, 1);
                        v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_3208_ = 1usize;
                        v___x_3209_ = lean_usize_add(v_i_3187_, v___x_3208_);
                        v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_3185_, v_sz_3186_, v___x_3209_, v___x_3207_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
                        return v___x_3210_;
                    } else {
                        v_a_3211_ = lean_ctor_get(v___x_3206_, 0);
                        v_isSharedCheck_3218_ = (!lean_is_exclusive(v___x_3206_)) as u8;
                        if v_isSharedCheck_3218_ == 0 {
                            v___x_3213_ = v___x_3206_;
                            v_isShared_3214_ = v_isSharedCheck_3218_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3211_);
                            lean_dec(v___x_3206_);
                            v___x_3213_ = lean_box(0);
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
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
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
    mut v_as_3219_: *mut LeanObject,
    mut v_sz_3220_: *mut LeanObject,
    mut v_i_3221_: *mut LeanObject,
    mut v_b_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
    mut v___y_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3235_: usize = 0;
    let mut v_i_boxed_3236_: usize = 0;
    let mut v_res_3237_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3235_ = lean_unbox_usize(v_sz_3220_);
    lean_dec(v_sz_3220_);
    v_i_boxed_3236_ = lean_unbox_usize(v_i_3221_);
    lean_dec(v_i_3221_);
    v_res_3237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_as_3219_, v_sz_boxed_3235_, v_i_boxed_3236_, v_b_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
    lean_dec(v___y_3233_);
    lean_dec_ref(v___y_3232_);
    lean_dec(v___y_3231_);
    lean_dec_ref(v___y_3230_);
    lean_dec(v___y_3229_);
    lean_dec_ref(v___y_3228_);
    lean_dec(v___y_3227_);
    lean_dec_ref(v___y_3226_);
    lean_dec(v___y_3225_);
    lean_dec(v___y_3224_);
    lean_dec(v___y_3223_);
    lean_dec_ref(v_as_3219_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(
    mut v_init_3238_: *mut LeanObject,
    mut v_n_3239_: *mut LeanObject,
    mut v_b_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3256_: usize = 0;
    let mut v___x_3257_: usize = 0;
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v_fst_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_vs_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3285_: usize = 0;
    let mut v___x_3286_: usize = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v_fst_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_a_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3306_: u8 = 0;
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_3239_) == 0 {
                    v_cs_3253_ = lean_ctor_get(v_n_3239_, 0);
                    v___x_3254_ = lean_box(0);
                    v___x_3255_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                    lean_ctor_set(v___x_3255_, 1, v_b_3240_);
                    v_sz_3256_ = lean_array_size(v_cs_3253_);
                    v___x_3257_ = 0usize;
                    v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_3238_, v_cs_3253_, v_sz_3256_, v___x_3257_, v___x_3255_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
                    if lean_obj_tag(v___x_3258_) == 0 {
                        v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
                        v_isSharedCheck_3273_ = (!lean_is_exclusive(v___x_3258_)) as u8;
                        if v_isSharedCheck_3273_ == 0 {
                            v___x_3261_ = v___x_3258_;
                            v_isShared_3262_ = v_isSharedCheck_3273_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3259_);
                            lean_dec(v___x_3258_);
                            v___x_3261_ = lean_box(0);
                            v_isShared_3262_ = v_isSharedCheck_3273_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3274_ = lean_ctor_get(v___x_3258_, 0);
                        v_isSharedCheck_3281_ = (!lean_is_exclusive(v___x_3258_)) as u8;
                        if v_isSharedCheck_3281_ == 0 {
                            v___x_3276_ = v___x_3258_;
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3274_);
                            lean_dec(v___x_3258_);
                            v___x_3276_ = lean_box(0);
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3282_ = lean_ctor_get(v_n_3239_, 0);
                    v___x_3283_ = lean_box(0);
                    v___x_3284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3284_, 0, v___x_3283_);
                    lean_ctor_set(v___x_3284_, 1, v_b_3240_);
                    v_sz_3285_ = lean_array_size(v_vs_3282_);
                    v___x_3286_ = 0usize;
                    v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_vs_3282_, v_sz_3285_, v___x_3286_, v___x_3284_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
                    if lean_obj_tag(v___x_3287_) == 0 {
                        v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
                        v_isSharedCheck_3302_ = (!lean_is_exclusive(v___x_3287_)) as u8;
                        if v_isSharedCheck_3302_ == 0 {
                            v___x_3290_ = v___x_3287_;
                            v_isShared_3291_ = v_isSharedCheck_3302_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3288_);
                            lean_dec(v___x_3287_);
                            v___x_3290_ = lean_box(0);
                            v_isShared_3291_ = v_isSharedCheck_3302_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3303_ = lean_ctor_get(v___x_3287_, 0);
                        v_isSharedCheck_3310_ = (!lean_is_exclusive(v___x_3287_)) as u8;
                        if v_isSharedCheck_3310_ == 0 {
                            v___x_3305_ = v___x_3287_;
                            v_isShared_3306_ = v_isSharedCheck_3310_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3303_);
                            lean_dec(v___x_3287_);
                            v___x_3305_ = lean_box(0);
                            v_isShared_3306_ = v_isSharedCheck_3310_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3263_ = lean_ctor_get(v_a_3259_, 0);
                if lean_obj_tag(v_fst_3263_) == 0 {
                    v_snd_3264_ = lean_ctor_get(v_a_3259_, 1);
                    lean_inc(v_snd_3264_);
                    lean_dec(v_a_3259_);
                    v___x_3265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3265_, 0, v_snd_3264_);
                    if v_isShared_3262_ == 0 {
                        lean_ctor_set(v___x_3261_, 0, v___x_3265_);
                        v___x_3267_ = v___x_3261_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
                        v___x_3267_ = v_reuseFailAlloc_3268_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3263_);
                    lean_dec(v_a_3259_);
                    v_val_3269_ = lean_ctor_get(v_fst_3263_, 0);
                    lean_inc(v_val_3269_);
                    lean_dec_ref_known(v_fst_3263_, 1);
                    if v_isShared_3262_ == 0 {
                        lean_ctor_set(v___x_3261_, 0, v_val_3269_);
                        v___x_3271_ = v___x_3261_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_val_3269_);
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
                    v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3279_;
            }
            6 => {
                v_fst_3292_ = lean_ctor_get(v_a_3288_, 0);
                if lean_obj_tag(v_fst_3292_) == 0 {
                    v_snd_3293_ = lean_ctor_get(v_a_3288_, 1);
                    lean_inc(v_snd_3293_);
                    lean_dec(v_a_3288_);
                    v___x_3294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3294_, 0, v_snd_3293_);
                    if v_isShared_3291_ == 0 {
                        lean_ctor_set(v___x_3290_, 0, v___x_3294_);
                        v___x_3296_ = v___x_3290_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
                        v___x_3296_ = v_reuseFailAlloc_3297_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3292_);
                    lean_dec(v_a_3288_);
                    v_val_3298_ = lean_ctor_get(v_fst_3292_, 0);
                    lean_inc(v_val_3298_);
                    lean_dec_ref_known(v_fst_3292_, 1);
                    if v_isShared_3291_ == 0 {
                        lean_ctor_set(v___x_3290_, 0, v_val_3298_);
                        v___x_3300_ = v___x_3290_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3298_);
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
                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
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
    mut v_init_3311_: *mut LeanObject,
    mut v_as_3312_: *mut LeanObject,
    mut v_sz_3313_: usize,
    mut v_i_3314_: usize,
    mut v_b_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v_reuseFailAlloc_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_usize_dec_lt(v_i_3314_, v_sz_3313_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3329_, 0, v_b_3315_);
                    return v___x_3329_;
                } else {
                    v_snd_3330_ = lean_ctor_get(v_b_3315_, 1);
                    v_isSharedCheck_3364_ = (!lean_is_exclusive(v_b_3315_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v_unused_3365_ = lean_ctor_get(v_b_3315_, 0);
                        lean_dec(v_unused_3365_);
                        v___x_3332_ = v_b_3315_;
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3330_);
                        lean_dec(v_b_3315_);
                        v___x_3332_ = lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3334_ = lean_array_uget_borrowed(v_as_3312_, v_i_3314_);
                lean_inc(v_snd_3330_);
                v___x_3335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3311_, v_a_3334_, v_snd_3330_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
                if lean_obj_tag(v___x_3335_) == 0 {
                    v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3355_ = (!lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3338_ = v___x_3335_;
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3336_);
                        lean_dec(v___x_3335_);
                        v___x_3338_ = lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3332_);
                    lean_dec(v_snd_3330_);
                    v_a_3356_ = lean_ctor_get(v___x_3335_, 0);
                    v_isSharedCheck_3363_ = (!lean_is_exclusive(v___x_3335_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3335_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3356_);
                        lean_dec(v___x_3335_);
                        v___x_3358_ = lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3336_) == 0 {
                    v___x_3340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3340_, 0, v_a_3336_);
                    if v_isShared_3333_ == 0 {
                        lean_ctor_set(v___x_3332_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                        lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3330_);
                        v___x_3342_ = v_reuseFailAlloc_3346_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3338_);
                    lean_dec(v_snd_3330_);
                    v_a_3347_ = lean_ctor_get(v_a_3336_, 0);
                    lean_inc(v_a_3347_);
                    lean_dec_ref_known(v_a_3336_, 1);
                    v___x_3348_ = lean_box(0);
                    if v_isShared_3333_ == 0 {
                        lean_ctor_set(v___x_3332_, 1, v_a_3347_);
                        lean_ctor_set(v___x_3332_, 0, v___x_3348_);
                        v___x_3350_ = v___x_3332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
                        lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3347_);
                        v___x_3350_ = v_reuseFailAlloc_3354_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3339_ == 0 {
                    lean_ctor_set(v___x_3338_, 0, v___x_3342_);
                    v___x_3344_ = v___x_3338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
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
                    v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_3366_: *mut LeanObject = *_args.add(0);
    let mut v_as_3367_: *mut LeanObject = *_args.add(1);
    let mut v_sz_3368_: *mut LeanObject = *_args.add(2);
    let mut v_i_3369_: *mut LeanObject = *_args.add(3);
    let mut v_b_3370_: *mut LeanObject = *_args.add(4);
    let mut v___y_3371_: *mut LeanObject = *_args.add(5);
    let mut v___y_3372_: *mut LeanObject = *_args.add(6);
    let mut v___y_3373_: *mut LeanObject = *_args.add(7);
    let mut v___y_3374_: *mut LeanObject = *_args.add(8);
    let mut v___y_3375_: *mut LeanObject = *_args.add(9);
    let mut v___y_3376_: *mut LeanObject = *_args.add(10);
    let mut v___y_3377_: *mut LeanObject = *_args.add(11);
    let mut v___y_3378_: *mut LeanObject = *_args.add(12);
    let mut v___y_3379_: *mut LeanObject = *_args.add(13);
    let mut v___y_3380_: *mut LeanObject = *_args.add(14);
    let mut v___y_3381_: *mut LeanObject = *_args.add(15);
    let mut v___y_3382_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_3383_: usize = 0;
    let mut v_i_boxed_3384_: usize = 0;
    let mut v_res_3385_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3383_ = lean_unbox_usize(v_sz_3368_);
    lean_dec(v_sz_3368_);
    v_i_boxed_3384_ = lean_unbox_usize(v_i_3369_);
    lean_dec(v_i_3369_);
    v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_3366_, v_as_3367_, v_sz_boxed_3383_, v_i_boxed_3384_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    lean_dec(v___y_3381_);
    lean_dec_ref(v___y_3380_);
    lean_dec(v___y_3379_);
    lean_dec_ref(v___y_3378_);
    lean_dec(v___y_3377_);
    lean_dec_ref(v___y_3376_);
    lean_dec(v___y_3375_);
    lean_dec_ref(v___y_3374_);
    lean_dec(v___y_3373_);
    lean_dec(v___y_3372_);
    lean_dec(v___y_3371_);
    lean_dec_ref(v_as_3367_);
    return v_res_3385_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(
    mut v_init_3386_: *mut LeanObject,
    mut v_n_3387_: *mut LeanObject,
    mut v_b_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3401_: *mut LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3386_, v_n_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
    lean_dec(v___y_3399_);
    lean_dec_ref(v___y_3398_);
    lean_dec(v___y_3397_);
    lean_dec_ref(v___y_3396_);
    lean_dec(v___y_3395_);
    lean_dec_ref(v___y_3394_);
    lean_dec(v___y_3393_);
    lean_dec_ref(v___y_3392_);
    lean_dec(v___y_3391_);
    lean_dec(v___y_3390_);
    lean_dec(v___y_3389_);
    lean_dec_ref(v_n_3387_);
    return v_res_3401_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(
    mut v_t_3402_: *mut LeanObject,
    mut v_init_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v_a_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v_fst_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3416_ = lean_ctor_get(v_t_3402_, 0);
                v_tail_3417_ = lean_ctor_get(v_t_3402_, 1);
                v___x_3418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_3403_, v_root_3416_, v_init_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
                if lean_obj_tag(v___x_3418_) == 0 {
                    v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3421_ = v___x_3418_;
                        v_isShared_3422_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3419_);
                        lean_dec(v___x_3418_);
                        v___x_3421_ = lean_box(0);
                        v_isShared_3422_ = v_isSharedCheck_3455_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3456_ = lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3463_ = (!lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3458_ = v___x_3418_;
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3456_);
                        lean_dec(v___x_3418_);
                        v___x_3458_ = lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3419_) == 0 {
                    v_a_3423_ = lean_ctor_get(v_a_3419_, 0);
                    lean_inc(v_a_3423_);
                    lean_dec_ref_known(v_a_3419_, 1);
                    if v_isShared_3422_ == 0 {
                        lean_ctor_set(v___x_3421_, 0, v_a_3423_);
                        v___x_3425_ = v___x_3421_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3423_);
                        v___x_3425_ = v_reuseFailAlloc_3426_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3421_);
                    v_a_3427_ = lean_ctor_get(v_a_3419_, 0);
                    lean_inc(v_a_3427_);
                    lean_dec_ref_known(v_a_3419_, 1);
                    v___x_3428_ = lean_box(0);
                    v___x_3429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3429_, 0, v___x_3428_);
                    lean_ctor_set(v___x_3429_, 1, v_a_3427_);
                    v_sz_3430_ = lean_array_size(v_tail_3417_);
                    v___x_3431_ = 0usize;
                    v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_tail_3417_, v_sz_3430_, v___x_3431_, v___x_3429_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
                    if lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3446_ = (!lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3446_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3433_);
                            lean_dec(v___x_3432_);
                            v___x_3435_ = lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3447_ = lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3454_ = (!lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3454_ == 0 {
                            v___x_3449_ = v___x_3432_;
                            v_isShared_3450_ = v_isSharedCheck_3454_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3447_);
                            lean_dec(v___x_3432_);
                            v___x_3449_ = lean_box(0);
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
                v_fst_3437_ = lean_ctor_get(v_a_3433_, 0);
                if lean_obj_tag(v_fst_3437_) == 0 {
                    v_snd_3438_ = lean_ctor_get(v_a_3433_, 1);
                    lean_inc(v_snd_3438_);
                    lean_dec(v_a_3433_);
                    if v_isShared_3436_ == 0 {
                        lean_ctor_set(v___x_3435_, 0, v_snd_3438_);
                        v___x_3440_ = v___x_3435_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_snd_3438_);
                        v___x_3440_ = v_reuseFailAlloc_3441_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3437_);
                    lean_dec(v_a_3433_);
                    v_val_3442_ = lean_ctor_get(v_fst_3437_, 0);
                    lean_inc(v_val_3442_);
                    lean_dec_ref_known(v_fst_3437_, 1);
                    if v_isShared_3436_ == 0 {
                        lean_ctor_set(v___x_3435_, 0, v_val_3442_);
                        v___x_3444_ = v___x_3435_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_val_3442_);
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
                    v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
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
                    v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
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
    mut v_t_3464_: *mut LeanObject,
    mut v_init_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3478_: *mut LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_t_3464_, v_init_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
    lean_dec(v___y_3476_);
    lean_dec_ref(v___y_3475_);
    lean_dec(v___y_3474_);
    lean_dec_ref(v___y_3473_);
    lean_dec(v___y_3472_);
    lean_dec_ref(v___y_3471_);
    lean_dec(v___y_3470_);
    lean_dec_ref(v___y_3469_);
    lean_dec(v___y_3468_);
    lean_dec(v___y_3467_);
    lean_dec(v___y_3466_);
    lean_dec_ref(v_t_3464_);
    return v_res_3478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
    mut v_a_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
    mut v_a_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v_unused_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3491_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_,
                    v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_,
                );
                if lean_obj_tag(v___x_3491_) == 0 {
                    v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
                    lean_inc(v_a_3492_);
                    lean_dec_ref_known(v___x_3491_, 1);
                    v_diseqs_3493_ = lean_ctor_get(v_a_3492_, 16);
                    lean_inc_ref(v_diseqs_3493_);
                    lean_dec(v_a_3492_);
                    v___x_3494_ = lean_box(0);
                    v___x_3495_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_diseqs_3493_, v___x_3494_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
                    lean_dec_ref(v_diseqs_3493_);
                    if lean_obj_tag(v___x_3495_) == 0 {
                        v_isSharedCheck_3502_ = (!lean_is_exclusive(v___x_3495_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v_unused_3503_ = lean_ctor_get(v___x_3495_, 0);
                            lean_dec(v_unused_3503_);
                            v___x_3497_ = v___x_3495_;
                            v_isShared_3498_ = v_isSharedCheck_3502_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3495_);
                            v___x_3497_ = lean_box(0);
                            v_isShared_3498_ = v_isSharedCheck_3502_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3495_;
                    }
                } else {
                    v_a_3504_ = lean_ctor_get(v___x_3491_, 0);
                    v_isSharedCheck_3511_ = (!lean_is_exclusive(v___x_3491_)) as u8;
                    if v_isSharedCheck_3511_ == 0 {
                        v___x_3506_ = v___x_3491_;
                        v_isShared_3507_ = v_isSharedCheck_3511_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3504_);
                        lean_dec(v___x_3491_);
                        v___x_3506_ = lean_box(0);
                        v_isShared_3507_ = v_isSharedCheck_3511_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3498_ == 0 {
                    lean_ctor_set(v___x_3497_, 0, v___x_3494_);
                    v___x_3500_ = v___x_3497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3494_);
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
                    v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
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
    mut v_a_3512_: *mut LeanObject,
    mut v_a_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
    mut v_a_3516_: *mut LeanObject,
    mut v_a_3517_: *mut LeanObject,
    mut v_a_3518_: *mut LeanObject,
    mut v_a_3519_: *mut LeanObject,
    mut v_a_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    v_res_3524_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(
        v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_,
        v_a_3520_, v_a_3521_, v_a_3522_,
    );
    lean_dec(v_a_3522_);
    lean_dec_ref(v_a_3521_);
    lean_dec(v_a_3520_);
    lean_dec_ref(v_a_3519_);
    lean_dec(v_a_3518_);
    lean_dec_ref(v_a_3517_);
    lean_dec(v_a_3516_);
    lean_dec_ref(v_a_3515_);
    lean_dec(v_a_3514_);
    lean_dec(v_a_3513_);
    lean_dec(v_a_3512_);
    return v_res_3524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
    mut v_a_3529_: *mut LeanObject,
    mut v_a_3530_: *mut LeanObject,
    mut v_a_3531_: *mut LeanObject,
    mut v_a_3532_: *mut LeanObject,
    mut v_a_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    v___x_3537_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(
        v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_,
        v_a_3533_, v_a_3534_, v_a_3535_,
    );
    if lean_obj_tag(v___x_3537_) == 0 {
        let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3537_, 1);
        v___x_3538_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(
            v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_,
            v_a_3533_, v_a_3534_, v_a_3535_,
        );
        if lean_obj_tag(v___x_3538_) == 0 {
            let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3538_, 1);
            v___x_3539_ =
                l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(
                    v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_,
                    v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_,
                );
            if lean_obj_tag(v___x_3539_) == 0 {
                let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_3539_, 1);
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
    mut v_a_3541_: *mut LeanObject,
    mut v_a_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
    mut v_a_3544_: *mut LeanObject,
    mut v_a_3545_: *mut LeanObject,
    mut v_a_3546_: *mut LeanObject,
    mut v_a_3547_: *mut LeanObject,
    mut v_a_3548_: *mut LeanObject,
    mut v_a_3549_: *mut LeanObject,
    mut v_a_3550_: *mut LeanObject,
    mut v_a_3551_: *mut LeanObject,
    mut v_a_3552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3553_: *mut LeanObject = core::ptr::null_mut();
    v_res_3553_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(
        v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_,
        v_a_3549_, v_a_3550_, v_a_3551_,
    );
    lean_dec(v_a_3551_);
    lean_dec_ref(v_a_3550_);
    lean_dec(v_a_3549_);
    lean_dec_ref(v_a_3548_);
    lean_dec(v_a_3547_);
    lean_dec_ref(v_a_3546_);
    lean_dec(v_a_3545_);
    lean_dec_ref(v_a_3544_);
    lean_dec(v_a_3543_);
    lean_dec(v_a_3542_);
    lean_dec(v_a_3541_);
    return v_res_3553_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(
    mut v_upperBound_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
    mut v_b_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3568_ = lean_nat_dec_lt(v_a_3555_, v_upperBound_3554_);
                if v___x_3568_ == 0 {
                    lean_dec(v_a_3555_);
                    v___x_3569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3569_, 0, v_b_3556_);
                    return v___x_3569_;
                } else {
                    v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_3555_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
                    if lean_obj_tag(v___x_3570_) == 0 {
                        lean_dec_ref_known(v___x_3570_, 1);
                        v___x_3571_ = lean_box(0);
                        v___x_3572_ = lean_unsigned_to_nat(1);
                        v___x_3573_ = lean_nat_add(v_a_3555_, v___x_3572_);
                        lean_dec(v_a_3555_);
                        v_a_3555_ = v___x_3573_;
                        v_b_3556_ = v___x_3571_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_3555_);
                        return v___x_3570_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_3575_: *mut LeanObject,
    mut v_a_3576_: *mut LeanObject,
    mut v_b_3577_: *mut LeanObject,
    mut v___y_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3589_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3587_);
    lean_dec_ref(v___y_3586_);
    lean_dec(v___y_3585_);
    lean_dec_ref(v___y_3584_);
    lean_dec(v___y_3583_);
    lean_dec_ref(v___y_3582_);
    lean_dec(v___y_3581_);
    lean_dec_ref(v___y_3580_);
    lean_dec(v___y_3579_);
    lean_dec(v___y_3578_);
    lean_dec(v_upperBound_3575_);
    return v_res_3589_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkInvariants(
    mut v_a_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
    mut v_a_3593_: *mut LeanObject,
    mut v_a_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_debug_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structs_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v_unused_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_3601_ = lean_ctor_get_uint8(
                    v_a_3592_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_3601_ == 0 {
                    v___x_3602_ = lean_box(0);
                    v___x_3603_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3603_, 0, v___x_3602_);
                    return v___x_3603_;
                } else {
                    v___x_3604_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_3590_, v_a_3598_);
                    if lean_obj_tag(v___x_3604_) == 0 {
                        v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
                        lean_inc(v_a_3605_);
                        lean_dec_ref_known(v___x_3604_, 1);
                        v_structs_3606_ = lean_ctor_get(v_a_3605_, 0);
                        lean_inc_ref(v_structs_3606_);
                        lean_dec(v_a_3605_);
                        v___x_3607_ = lean_array_get_size(v_structs_3606_);
                        lean_dec_ref(v_structs_3606_);
                        v___x_3608_ = lean_unsigned_to_nat(0);
                        v___x_3609_ = lean_box(0);
                        v___x_3610_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v___x_3607_, v___x_3608_, v___x_3609_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
                        if lean_obj_tag(v___x_3610_) == 0 {
                            v_isSharedCheck_3617_ = (!lean_is_exclusive(v___x_3610_)) as u8;
                            if v_isSharedCheck_3617_ == 0 {
                                v_unused_3618_ = lean_ctor_get(v___x_3610_, 0);
                                lean_dec(v_unused_3618_);
                                v___x_3612_ = v___x_3610_;
                                v_isShared_3613_ = v_isSharedCheck_3617_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_3610_);
                                v___x_3612_ = lean_box(0);
                                v_isShared_3613_ = v_isSharedCheck_3617_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3610_;
                        }
                    } else {
                        v_a_3619_ = lean_ctor_get(v___x_3604_, 0);
                        v_isSharedCheck_3626_ = (!lean_is_exclusive(v___x_3604_)) as u8;
                        if v_isSharedCheck_3626_ == 0 {
                            v___x_3621_ = v___x_3604_;
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3619_);
                            lean_dec(v___x_3604_);
                            v___x_3621_ = lean_box(0);
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3613_ == 0 {
                    lean_ctor_set(v___x_3612_, 0, v___x_3609_);
                    v___x_3615_ = v___x_3612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3609_);
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
                    v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
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
    mut v_a_3627_: *mut LeanObject,
    mut v_a_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
    mut v_a_3632_: *mut LeanObject,
    mut v_a_3633_: *mut LeanObject,
    mut v_a_3634_: *mut LeanObject,
    mut v_a_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3638_: *mut LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_Lean_Meta_Grind_AC_checkInvariants(
        v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_,
        v_a_3635_, v_a_3636_,
    );
    lean_dec(v_a_3636_);
    lean_dec_ref(v_a_3635_);
    lean_dec(v_a_3634_);
    lean_dec_ref(v_a_3633_);
    lean_dec(v_a_3632_);
    lean_dec_ref(v_a_3631_);
    lean_dec(v_a_3630_);
    lean_dec_ref(v_a_3629_);
    lean_dec(v_a_3628_);
    lean_dec(v_a_3627_);
    return v_res_3638_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(
    mut v_upperBound_3639_: *mut LeanObject,
    mut v_inst_3640_: *mut LeanObject,
    mut v_R_3641_: *mut LeanObject,
    mut v_a_3642_: *mut LeanObject,
    mut v_b_3643_: *mut LeanObject,
    mut v_c_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_3657_: *mut LeanObject = *_args.add(0);
    let mut v_inst_3658_: *mut LeanObject = *_args.add(1);
    let mut v_R_3659_: *mut LeanObject = *_args.add(2);
    let mut v_a_3660_: *mut LeanObject = *_args.add(3);
    let mut v_b_3661_: *mut LeanObject = *_args.add(4);
    let mut v_c_3662_: *mut LeanObject = *_args.add(5);
    let mut v___y_3663_: *mut LeanObject = *_args.add(6);
    let mut v___y_3664_: *mut LeanObject = *_args.add(7);
    let mut v___y_3665_: *mut LeanObject = *_args.add(8);
    let mut v___y_3666_: *mut LeanObject = *_args.add(9);
    let mut v___y_3667_: *mut LeanObject = *_args.add(10);
    let mut v___y_3668_: *mut LeanObject = *_args.add(11);
    let mut v___y_3669_: *mut LeanObject = *_args.add(12);
    let mut v___y_3670_: *mut LeanObject = *_args.add(13);
    let mut v___y_3671_: *mut LeanObject = *_args.add(14);
    let mut v___y_3672_: *mut LeanObject = *_args.add(15);
    let mut v___y_3673_: *mut LeanObject = *_args.add(16);
    let mut v_res_3674_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3672_);
    lean_dec_ref(v___y_3671_);
    lean_dec(v___y_3670_);
    lean_dec_ref(v___y_3669_);
    lean_dec(v___y_3668_);
    lean_dec_ref(v___y_3667_);
    lean_dec(v___y_3666_);
    lean_dec_ref(v___y_3665_);
    lean_dec(v___y_3664_);
    lean_dec(v___y_3663_);
    lean_dec(v_upperBound_3657_);
    return v_res_3674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
}
