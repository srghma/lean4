// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Proof
// Imports: Lean.Meta.Tactic.Grind.Order.OrderM Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Init.Grind.Order
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Grind::Order::{
    initialize_Init_Grind_Order, runtime_initialize_Init_Grind_Order,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_instInhabitedForall___redArg___lam__0___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_eagerReflBoolTrue,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp6,
    l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEqTrue;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::OrderM::{
    initialize_Lean_Meta_Tactic_Grind_Order_OrderM, l_Lean_Meta_Grind_Order_getStruct,
    l_Lean_Meta_Grind_Order_isRing, runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_instInhabitedGoalM;
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_lt, lean_panic_fn_borrowed};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_12, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value) as *mut LeanObject,12648290874539584503 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 95, 108, 116, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value) as *mut LeanObject,7826207489827013974 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 116, 95, 108, 101, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value) as *mut LeanObject,16697182562648691278 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 116, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value) as *mut LeanObject,13335477371899428046 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value) as *mut LeanObject,17185717442815859305 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value) as *mut LeanObject,6362876895233142233 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value) as *mut LeanObject,15439129730316893054 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 101, 95, 108, 116, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value) as *mut LeanObject,2034847181816423711 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 116, 95, 108, 101, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value) as *mut LeanObject,3517412897252186849 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 116, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value) as *mut LeanObject,8748413887631389279 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value: LeanStringObject<95> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 95, m_capacity: 95, m_length: 94, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 69, 113, 84, 114, 117, 101, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 107, 46, 115, 116, 114, 105, 99, 116, 32, 38, 38, 32, 33, 107, 39, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value) as *mut LeanObject,17868538397656873279 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value) as *mut LeanObject,3762829983402653789 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value) as *mut LeanObject,11946608431158487874 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value) as *mut LeanObject,2174632405960423778 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value) as *mut LeanObject,2356419264488831487 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value) as *mut LeanObject,15156543457094102168 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value) as *mut LeanObject,6162781165823963266 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value) as *mut LeanObject,665796189504554409 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value: LeanStringObject<
    49,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101,
        114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 83, 101, 108, 102, 69, 113,
        84, 114, 117, 101, 80, 114, 111, 111, 102, 0,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value: LeanStringObject<
    36,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 33, 107, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value: LeanStringObject<96> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 69, 113, 70, 97, 108, 115, 101, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value) as *mut LeanObject,11397426148428336704 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value) as *mut LeanObject,17381615769107464045 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value) as *mut LeanObject,9508759425124742748 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value) as *mut LeanObject,18346083057132032349 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value) as *mut LeanObject,2795168870708388791 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value) as *mut LeanObject,4267366299720466442 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value) as *mut LeanObject,3722890380639652857 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value) as *mut LeanObject,16327706374038483011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value) as *mut LeanObject,11594183309238561488 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value) as *mut LeanObject,5295434444198197881 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value: LeanStringObject<
    50,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101,
        114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 83, 101, 108, 102, 69, 113,
        70, 97, 108, 115, 101, 80, 114, 111, 111, 102, 0,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value: LeanStringObject<
    35,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 107, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 116, 95, 117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value) as *mut LeanObject,18396075358907067085 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 117, 110, 115, 97, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value) as *mut LeanObject,13458098464594315830 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 116, 95, 117, 110, 115, 97, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value) as *mut LeanObject,952555606817756140 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value: LeanStringObject<85> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 85, 110, 115, 97, 116, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 46, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 107, 226, 130, 129, 46, 115, 116, 114, 105, 99, 116, 32, 124, 124, 32, 107, 226, 130, 130, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 113, 95, 111, 102, 95, 108, 101, 95, 111, 102, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value)
                as *mut LeanObject,
            4555975883093562615 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            101, 113, 95, 111, 102, 95, 108, 101, 95, 111, 102, 95, 108, 101, 95, 48, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut LeanObject,1686519415633536789 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value)
                as *mut LeanObject,
            2483426619224618075 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Order_mkLePreorderPrefix(
    mut v_declName_2274_: *mut LeanObject,
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
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_type_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_a_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2287_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_,
                    v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_,
                );
                if lean_obj_tag(v___x_2287_) == 0 {
                    v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2303_ = (!lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v___x_2290_ = v___x_2287_;
                        v_isShared_2291_ = v_isSharedCheck_2303_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2288_);
                        lean_dec(v___x_2287_);
                        v___x_2290_ = lean_box(0);
                        v_isShared_2291_ = v_isSharedCheck_2303_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_2274_);
                    v_a_2304_ = lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2311_ = (!lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2311_ == 0 {
                        v___x_2306_ = v___x_2287_;
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2304_);
                        lean_dec(v___x_2287_);
                        v___x_2306_ = lean_box(0);
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2292_ = lean_ctor_get(v_a_2288_, 1);
                lean_inc_ref(v_type_2292_);
                v_u_2293_ = lean_ctor_get(v_a_2288_, 2);
                lean_inc(v_u_2293_);
                v_isPreorderInst_2294_ = lean_ctor_get(v_a_2288_, 3);
                lean_inc_ref(v_isPreorderInst_2294_);
                v_leInst_2295_ = lean_ctor_get(v_a_2288_, 4);
                lean_inc_ref(v_leInst_2295_);
                lean_dec(v_a_2288_);
                v___x_2296_ = lean_box(0);
                v___x_2297_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2297_, 0, v_u_2293_);
                lean_ctor_set(v___x_2297_, 1, v___x_2296_);
                v___x_2298_ = l_Lean_mkConst(v_declName_2274_, v___x_2297_);
                v___x_2299_ = l_Lean_mkApp3(
                    v___x_2298_,
                    v_type_2292_,
                    v_leInst_2295_,
                    v_isPreorderInst_2294_,
                );
                if v_isShared_2291_ == 0 {
                    lean_ctor_set(v___x_2290_, 0, v___x_2299_);
                    v___x_2301_ = v___x_2290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
                    v___x_2301_ = v_reuseFailAlloc_2302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2301_;
            }
            3 => {
                if v_isShared_2307_ == 0 {
                    v___x_2309_ = v___x_2306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
                    v___x_2309_ = v_reuseFailAlloc_2310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLePreorderPrefix___boxed(
    mut v_declName_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
    mut v_a_2314_: *mut LeanObject,
    mut v_a_2315_: *mut LeanObject,
    mut v_a_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_a_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
    mut v_a_2321_: *mut LeanObject,
    mut v_a_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2325_: *mut LeanObject = core::ptr::null_mut();
    v_res_2325_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(
        v_declName_2312_,
        v_a_2313_,
        v_a_2314_,
        v_a_2315_,
        v_a_2316_,
        v_a_2317_,
        v_a_2318_,
        v_a_2319_,
        v_a_2320_,
        v_a_2321_,
        v_a_2322_,
        v_a_2323_,
    );
    lean_dec(v_a_2323_);
    lean_dec_ref(v_a_2322_);
    lean_dec(v_a_2321_);
    lean_dec_ref(v_a_2320_);
    lean_dec(v_a_2319_);
    lean_dec_ref(v_a_2318_);
    lean_dec(v_a_2317_);
    lean_dec_ref(v_a_2316_);
    lean_dec(v_a_2315_);
    lean_dec(v_a_2314_);
    lean_dec(v_a_2313_);
    return v_res_2325_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(
    mut v_msg_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lean_instInhabitedExpr;
    v___x_2328_ = lean_panic_fn_borrowed(v___x_2327_, v_msg_2326_);
    return v___x_2328_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3()
-> *mut LeanObject {
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v___x_2332_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2;
    v___x_2333_ = lean_unsigned_to_nat(14);
    v___x_2334_ = lean_unsigned_to_nat(22);
    v___x_2335_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1;
    v___x_2336_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0;
    v___x_2337_ = l_mkPanicMessageWithDecl(
        v___x_2336_,
        v___x_2335_,
        v___x_2334_,
        v___x_2333_,
        v___x_2332_,
    );
    return v___x_2337_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(
    mut v_declName_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
    mut v_a_2341_: *mut LeanObject,
    mut v_a_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_a_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v_type_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPartialInst_x3f_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v_a_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_,
                    v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_,
                );
                if lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2372_ = (!lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2372_ == 0 {
                        v___x_2354_ = v___x_2351_;
                        v_isShared_2355_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2352_);
                        lean_dec(v___x_2351_);
                        v___x_2354_ = lean_box(0);
                        v_isShared_2355_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_2338_);
                    v_a_2373_ = lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2380_ = (!lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2375_ = v___x_2351_;
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2373_);
                        lean_dec(v___x_2351_);
                        v___x_2375_ = lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2356_ = lean_ctor_get(v_a_2352_, 1);
                lean_inc_ref(v_type_2356_);
                v_u_2357_ = lean_ctor_get(v_a_2352_, 2);
                lean_inc(v_u_2357_);
                v_leInst_2358_ = lean_ctor_get(v_a_2352_, 4);
                lean_inc_ref(v_leInst_2358_);
                v_isPartialInst_x3f_2359_ = lean_ctor_get(v_a_2352_, 6);
                lean_inc(v_isPartialInst_x3f_2359_);
                lean_dec(v_a_2352_);
                v___x_2360_ = lean_box(0);
                v___x_2361_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2361_, 0, v_u_2357_);
                lean_ctor_set(v___x_2361_, 1, v___x_2360_);
                v___x_2362_ = l_Lean_mkConst(v_declName_2338_, v___x_2361_);
                if lean_obj_tag(v_isPartialInst_x3f_2359_) == 0 {
                    v___x_2369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2370_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2369_);
                    v___y_2364_ = v___x_2370_;
                    state = 2;
                    continue;
                } else {
                    v_val_2371_ = lean_ctor_get(v_isPartialInst_x3f_2359_, 0);
                    lean_inc(v_val_2371_);
                    lean_dec_ref_known(v_isPartialInst_x3f_2359_, 1);
                    v___y_2364_ = v_val_2371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2365_ = l_Lean_mkApp3(v___x_2362_, v_type_2356_, v_leInst_2358_, v___y_2364_);
                if v_isShared_2355_ == 0 {
                    lean_ctor_set(v___x_2354_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
                    v___x_2367_ = v_reuseFailAlloc_2368_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2367_;
            }
            4 => {
                if v_isShared_2376_ == 0 {
                    v___x_2378_ = v___x_2375_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___boxed(
    mut v_declName_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
    mut v_a_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2394_: *mut LeanObject = core::ptr::null_mut();
    v_res_2394_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(
            v_declName_2381_,
            v_a_2382_,
            v_a_2383_,
            v_a_2384_,
            v_a_2385_,
            v_a_2386_,
            v_a_2387_,
            v_a_2388_,
            v_a_2389_,
            v_a_2390_,
            v_a_2391_,
            v_a_2392_,
        );
    lean_dec(v_a_2392_);
    lean_dec_ref(v_a_2391_);
    lean_dec(v_a_2390_);
    lean_dec_ref(v_a_2389_);
    lean_dec(v_a_2388_);
    lean_dec_ref(v_a_2387_);
    lean_dec(v_a_2386_);
    lean_dec_ref(v_a_2385_);
    lean_dec(v_a_2384_);
    lean_dec(v_a_2383_);
    lean_dec(v_a_2382_);
    return v_res_2394_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(
    mut v_declName_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
    mut v_a_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
    mut v_a_2405_: *mut LeanObject,
    mut v_a_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v_type_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2436_: u8 = 0;
    let mut v_a_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2408_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_,
                    v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_,
                );
                if lean_obj_tag(v___x_2408_) == 0 {
                    v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
                    v_isSharedCheck_2436_ = (!lean_is_exclusive(v___x_2408_)) as u8;
                    if v_isSharedCheck_2436_ == 0 {
                        v___x_2411_ = v___x_2408_;
                        v_isShared_2412_ = v_isSharedCheck_2436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2409_);
                        lean_dec(v___x_2408_);
                        v___x_2411_ = lean_box(0);
                        v_isShared_2412_ = v_isSharedCheck_2436_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_2395_);
                    v_a_2437_ = lean_ctor_get(v___x_2408_, 0);
                    v_isSharedCheck_2444_ = (!lean_is_exclusive(v___x_2408_)) as u8;
                    if v_isSharedCheck_2444_ == 0 {
                        v___x_2439_ = v___x_2408_;
                        v_isShared_2440_ = v_isSharedCheck_2444_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2437_);
                        lean_dec(v___x_2408_);
                        v___x_2439_ = lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2444_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2413_ = lean_ctor_get(v_a_2409_, 1);
                lean_inc_ref(v_type_2413_);
                v_u_2414_ = lean_ctor_get(v_a_2409_, 2);
                lean_inc(v_u_2414_);
                v_leInst_2415_ = lean_ctor_get(v_a_2409_, 4);
                lean_inc_ref(v_leInst_2415_);
                v_ltInst_x3f_2416_ = lean_ctor_get(v_a_2409_, 5);
                lean_inc(v_ltInst_x3f_2416_);
                v_lawfulOrderLTInst_x3f_2417_ = lean_ctor_get(v_a_2409_, 8);
                lean_inc(v_lawfulOrderLTInst_x3f_2417_);
                lean_dec(v_a_2409_);
                v___x_2418_ = lean_box(0);
                v___x_2419_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2419_, 0, v_u_2414_);
                lean_ctor_set(v___x_2419_, 1, v___x_2418_);
                v___x_2420_ = l_Lean_mkConst(v_declName_2395_, v___x_2419_);
                if lean_obj_tag(v_ltInst_x3f_2416_) == 0 {
                    v___x_2433_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2434_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2433_);
                    v___y_2429_ = v___x_2434_;
                    state = 4;
                    continue;
                } else {
                    v_val_2435_ = lean_ctor_get(v_ltInst_x3f_2416_, 0);
                    lean_inc(v_val_2435_);
                    lean_dec_ref_known(v_ltInst_x3f_2416_, 1);
                    v___y_2429_ = v_val_2435_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2424_ = l_Lean_mkApp4(
                    v___x_2420_,
                    v_type_2413_,
                    v_leInst_2415_,
                    v___y_2422_,
                    v___y_2423_,
                );
                if v_isShared_2412_ == 0 {
                    lean_ctor_set(v___x_2411_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2411_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2426_;
            }
            4 => {
                if lean_obj_tag(v_lawfulOrderLTInst_x3f_2417_) == 0 {
                    v___x_2430_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2431_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2430_);
                    v___y_2422_ = v___y_2429_;
                    v___y_2423_ = v___x_2431_;
                    state = 2;
                    continue;
                } else {
                    v_val_2432_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_2417_, 0);
                    lean_inc(v_val_2432_);
                    lean_dec_ref_known(v_lawfulOrderLTInst_x3f_2417_, 1);
                    v___y_2422_ = v___y_2429_;
                    v___y_2423_ = v_val_2432_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2440_ == 0 {
                    v___x_2442_ = v___x_2439_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
                    v___x_2442_ = v_reuseFailAlloc_2443_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix___boxed(
    mut v_declName_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2458_: *mut LeanObject = core::ptr::null_mut();
    v_res_2458_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(
            v_declName_2445_,
            v_a_2446_,
            v_a_2447_,
            v_a_2448_,
            v_a_2449_,
            v_a_2450_,
            v_a_2451_,
            v_a_2452_,
            v_a_2453_,
            v_a_2454_,
            v_a_2455_,
            v_a_2456_,
        );
    lean_dec(v_a_2456_);
    lean_dec_ref(v_a_2455_);
    lean_dec(v_a_2454_);
    lean_dec_ref(v_a_2453_);
    lean_dec(v_a_2452_);
    lean_dec_ref(v_a_2451_);
    lean_dec(v_a_2450_);
    lean_dec_ref(v_a_2449_);
    lean_dec(v_a_2448_);
    lean_dec(v_a_2447_);
    lean_dec(v_a_2446_);
    return v_res_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(
    mut v_declName_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_a_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v_isPreorderInst_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_a_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2472_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_,
                    v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_,
                );
                if lean_obj_tag(v___x_2472_) == 0 {
                    v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
                    lean_inc(v_a_2473_);
                    lean_dec_ref_known(v___x_2472_, 1);
                    v___x_2474_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2474_) == 0 {
                        v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
                        v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2474_)) as u8;
                        if v_isSharedCheck_2484_ == 0 {
                            v___x_2477_ = v___x_2474_;
                            v_isShared_2478_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2475_);
                            lean_dec(v___x_2474_);
                            v___x_2477_ = lean_box(0);
                            v_isShared_2478_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2473_);
                        return v___x_2474_;
                    }
                } else {
                    lean_dec(v_declName_2459_);
                    v_a_2485_ = lean_ctor_get(v___x_2472_, 0);
                    v_isSharedCheck_2492_ = (!lean_is_exclusive(v___x_2472_)) as u8;
                    if v_isSharedCheck_2492_ == 0 {
                        v___x_2487_ = v___x_2472_;
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2485_);
                        lean_dec(v___x_2472_);
                        v___x_2487_ = lean_box(0);
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_isPreorderInst_2479_ = lean_ctor_get(v_a_2473_, 3);
                lean_inc_ref(v_isPreorderInst_2479_);
                lean_dec(v_a_2473_);
                v___x_2480_ = l_Lean_Expr_app___override(v_a_2475_, v_isPreorderInst_2479_);
                if v_isShared_2478_ == 0 {
                    lean_ctor_set(v___x_2477_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2482_;
            }
            3 => {
                if v_isShared_2488_ == 0 {
                    v___x_2490_ = v___x_2487_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
                    v___x_2490_ = v_reuseFailAlloc_2491_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix___boxed(
    mut v_declName_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2506_: *mut LeanObject = core::ptr::null_mut();
    v_res_2506_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
    lean_dec(v_a_2504_);
    lean_dec_ref(v_a_2503_);
    lean_dec(v_a_2502_);
    lean_dec_ref(v_a_2501_);
    lean_dec(v_a_2500_);
    lean_dec_ref(v_a_2499_);
    lean_dec(v_a_2498_);
    lean_dec_ref(v_a_2497_);
    lean_dec(v_a_2496_);
    lean_dec(v_a_2495_);
    lean_dec(v_a_2494_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(
    mut v_declName_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
    mut v_a_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___y_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearPreInst_x3f_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v_a_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2520_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_,
                    v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_,
                );
                if lean_obj_tag(v___x_2520_) == 0 {
                    v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
                    lean_inc(v_a_2521_);
                    lean_dec_ref_known(v___x_2520_, 1);
                    v___x_2522_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
                    if lean_obj_tag(v___x_2522_) == 0 {
                        v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
                        v_isSharedCheck_2537_ = (!lean_is_exclusive(v___x_2522_)) as u8;
                        if v_isSharedCheck_2537_ == 0 {
                            v___x_2525_ = v___x_2522_;
                            v_isShared_2526_ = v_isSharedCheck_2537_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2523_);
                            lean_dec(v___x_2522_);
                            v___x_2525_ = lean_box(0);
                            v_isShared_2526_ = v_isSharedCheck_2537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2521_);
                        return v___x_2522_;
                    }
                } else {
                    lean_dec(v_declName_2507_);
                    v_a_2538_ = lean_ctor_get(v___x_2520_, 0);
                    v_isSharedCheck_2545_ = (!lean_is_exclusive(v___x_2520_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v___x_2540_ = v___x_2520_;
                        v_isShared_2541_ = v_isSharedCheck_2545_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2538_);
                        lean_dec(v___x_2520_);
                        v___x_2540_ = lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2545_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearPreInst_x3f_2533_ = lean_ctor_get(v_a_2521_, 7);
                lean_inc(v_isLinearPreInst_x3f_2533_);
                lean_dec(v_a_2521_);
                if lean_obj_tag(v_isLinearPreInst_x3f_2533_) == 0 {
                    v___x_2534_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2535_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2534_);
                    v___y_2528_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_val_2536_ = lean_ctor_get(v_isLinearPreInst_x3f_2533_, 0);
                    lean_inc(v_val_2536_);
                    lean_dec_ref_known(v_isLinearPreInst_x3f_2533_, 1);
                    v___y_2528_ = v_val_2536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2529_ = l_Lean_Expr_app___override(v_a_2523_, v___y_2528_);
                if v_isShared_2526_ == 0 {
                    lean_ctor_set(v___x_2525_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    v___x_2531_ = v_reuseFailAlloc_2532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2531_;
            }
            4 => {
                if v_isShared_2541_ == 0 {
                    v___x_2543_ = v___x_2540_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
                    v___x_2543_ = v_reuseFailAlloc_2544_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix___boxed(
    mut v_declName_2546_: *mut LeanObject,
    mut v_a_2547_: *mut LeanObject,
    mut v_a_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
    mut v_a_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
    mut v_a_2556_: *mut LeanObject,
    mut v_a_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2559_: *mut LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(
        v_declName_2546_,
        v_a_2547_,
        v_a_2548_,
        v_a_2549_,
        v_a_2550_,
        v_a_2551_,
        v_a_2552_,
        v_a_2553_,
        v_a_2554_,
        v_a_2555_,
        v_a_2556_,
        v_a_2557_,
    );
    lean_dec(v_a_2557_);
    lean_dec_ref(v_a_2556_);
    lean_dec(v_a_2555_);
    lean_dec_ref(v_a_2554_);
    lean_dec(v_a_2553_);
    lean_dec_ref(v_a_2552_);
    lean_dec(v_a_2551_);
    lean_dec_ref(v_a_2550_);
    lean_dec(v_a_2549_);
    lean_dec(v_a_2548_);
    lean_dec(v_a_2547_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLinearPrefix(
    mut v_declName_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_a_2562_: *mut LeanObject,
    mut v_a_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
    mut v_a_2565_: *mut LeanObject,
    mut v_a_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
    mut v_a_2570_: *mut LeanObject,
    mut v_a_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v_type_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearPreInst_x3f_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v_a_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2573_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_,
                    v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_,
                );
                if lean_obj_tag(v___x_2573_) == 0 {
                    v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2594_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2594_ == 0 {
                        v___x_2576_ = v___x_2573_;
                        v_isShared_2577_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2574_);
                        lean_dec(v___x_2573_);
                        v___x_2576_ = lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_2560_);
                    v_a_2595_ = lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2602_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2597_ = v___x_2573_;
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2595_);
                        lean_dec(v___x_2573_);
                        v___x_2597_ = lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2578_ = lean_ctor_get(v_a_2574_, 1);
                lean_inc_ref(v_type_2578_);
                v_u_2579_ = lean_ctor_get(v_a_2574_, 2);
                lean_inc(v_u_2579_);
                v_leInst_2580_ = lean_ctor_get(v_a_2574_, 4);
                lean_inc_ref(v_leInst_2580_);
                v_isLinearPreInst_x3f_2581_ = lean_ctor_get(v_a_2574_, 7);
                lean_inc(v_isLinearPreInst_x3f_2581_);
                lean_dec(v_a_2574_);
                v___x_2582_ = lean_box(0);
                v___x_2583_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2583_, 0, v_u_2579_);
                lean_ctor_set(v___x_2583_, 1, v___x_2582_);
                v___x_2584_ = l_Lean_mkConst(v_declName_2560_, v___x_2583_);
                if lean_obj_tag(v_isLinearPreInst_x3f_2581_) == 0 {
                    v___x_2591_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2592_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2591_);
                    v___y_2586_ = v___x_2592_;
                    state = 2;
                    continue;
                } else {
                    v_val_2593_ = lean_ctor_get(v_isLinearPreInst_x3f_2581_, 0);
                    lean_inc(v_val_2593_);
                    lean_dec_ref_known(v_isLinearPreInst_x3f_2581_, 1);
                    v___y_2586_ = v_val_2593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2587_ = l_Lean_mkApp3(v___x_2584_, v_type_2578_, v_leInst_2580_, v___y_2586_);
                if v_isShared_2577_ == 0 {
                    lean_ctor_set(v___x_2576_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2589_;
            }
            4 => {
                if v_isShared_2598_ == 0 {
                    v___x_2600_ = v___x_2597_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
                    v___x_2600_ = v_reuseFailAlloc_2601_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLinearPrefix___boxed(
    mut v_declName_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2616_: *mut LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(
        v_declName_2603_,
        v_a_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
        v_a_2608_,
        v_a_2609_,
        v_a_2610_,
        v_a_2611_,
        v_a_2612_,
        v_a_2613_,
        v_a_2614_,
    );
    lean_dec(v_a_2614_);
    lean_dec_ref(v_a_2613_);
    lean_dec(v_a_2612_);
    lean_dec_ref(v_a_2611_);
    lean_dec(v_a_2610_);
    lean_dec_ref(v_a_2609_);
    lean_dec(v_a_2608_);
    lean_dec_ref(v_a_2607_);
    lean_dec(v_a_2606_);
    lean_dec(v_a_2605_);
    lean_dec(v_a_2604_);
    return v_res_2616_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
    mut v_declName_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v___y_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_a_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_,
                    v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_,
                );
                if lean_obj_tag(v___x_2630_) == 0 {
                    v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
                    lean_inc(v_a_2631_);
                    lean_dec_ref_known(v___x_2630_, 1);
                    v___x_2632_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
                    if lean_obj_tag(v___x_2632_) == 0 {
                        v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
                        v_isSharedCheck_2654_ = (!lean_is_exclusive(v___x_2632_)) as u8;
                        if v_isSharedCheck_2654_ == 0 {
                            v___x_2635_ = v___x_2632_;
                            v_isShared_2636_ = v_isSharedCheck_2654_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2633_);
                            lean_dec(v___x_2632_);
                            v___x_2635_ = lean_box(0);
                            v_isShared_2636_ = v_isSharedCheck_2654_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2631_);
                        return v___x_2632_;
                    }
                } else {
                    lean_dec(v_declName_2617_);
                    v_a_2655_ = lean_ctor_get(v___x_2630_, 0);
                    v_isSharedCheck_2662_ = (!lean_is_exclusive(v___x_2630_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2657_ = v___x_2630_;
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2655_);
                        lean_dec(v___x_2630_);
                        v___x_2657_ = lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringInst_x3f_2644_ = lean_ctor_get(v_a_2631_, 10);
                lean_inc(v_ringInst_x3f_2644_);
                v_orderedRingInst_x3f_2645_ = lean_ctor_get(v_a_2631_, 11);
                lean_inc(v_orderedRingInst_x3f_2645_);
                lean_dec(v_a_2631_);
                if lean_obj_tag(v_ringInst_x3f_2644_) == 0 {
                    v___x_2651_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2652_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2651_);
                    v___y_2647_ = v___x_2652_;
                    state = 4;
                    continue;
                } else {
                    v_val_2653_ = lean_ctor_get(v_ringInst_x3f_2644_, 0);
                    lean_inc(v_val_2653_);
                    lean_dec_ref_known(v_ringInst_x3f_2644_, 1);
                    v___y_2647_ = v_val_2653_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = l_Lean_mkAppB(v_a_2633_, v___y_2638_, v___y_2639_);
                if v_isShared_2636_ == 0 {
                    lean_ctor_set(v___x_2635_, 0, v___x_2640_);
                    v___x_2642_ = v___x_2635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
                    v___x_2642_ = v_reuseFailAlloc_2643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2642_;
            }
            4 => {
                if lean_obj_tag(v_orderedRingInst_x3f_2645_) == 0 {
                    v___x_2648_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2649_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2648_);
                    v___y_2638_ = v___y_2647_;
                    v___y_2639_ = v___x_2649_;
                    state = 2;
                    continue;
                } else {
                    v_val_2650_ = lean_ctor_get(v_orderedRingInst_x3f_2645_, 0);
                    lean_inc(v_val_2650_);
                    lean_dec_ref_known(v_orderedRingInst_x3f_2645_, 1);
                    v___y_2638_ = v___y_2647_;
                    v___y_2639_ = v_val_2650_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2658_ == 0 {
                    v___x_2660_ = v___x_2657_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
                    v___x_2660_ = v_reuseFailAlloc_2661_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkOrdRingPrefix___boxed(
    mut v_declName_2663_: *mut LeanObject,
    mut v_a_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
    mut v_a_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
    mut v_a_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2676_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
        v_declName_2663_,
        v_a_2664_,
        v_a_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
        v_a_2669_,
        v_a_2670_,
        v_a_2671_,
        v_a_2672_,
        v_a_2673_,
        v_a_2674_,
    );
    lean_dec(v_a_2674_);
    lean_dec_ref(v_a_2673_);
    lean_dec(v_a_2672_);
    lean_dec_ref(v_a_2671_);
    lean_dec(v_a_2670_);
    lean_dec_ref(v_a_2669_);
    lean_dec(v_a_2668_);
    lean_dec_ref(v_a_2667_);
    lean_dec(v_a_2666_);
    lean_dec(v_a_2665_);
    lean_dec(v_a_2664_);
    return v_res_2676_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(
    mut v_declName_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___y_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_a_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2690_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_,
                    v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_,
                );
                if lean_obj_tag(v___x_2690_) == 0 {
                    v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
                    lean_inc(v_a_2691_);
                    lean_dec_ref_known(v___x_2690_, 1);
                    v___x_2692_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(
                        v_declName_2677_,
                        v_a_2678_,
                        v_a_2679_,
                        v_a_2680_,
                        v_a_2681_,
                        v_a_2682_,
                        v_a_2683_,
                        v_a_2684_,
                        v_a_2685_,
                        v_a_2686_,
                        v_a_2687_,
                        v_a_2688_,
                    );
                    if lean_obj_tag(v___x_2692_) == 0 {
                        v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
                        v_isSharedCheck_2714_ = (!lean_is_exclusive(v___x_2692_)) as u8;
                        if v_isSharedCheck_2714_ == 0 {
                            v___x_2695_ = v___x_2692_;
                            v_isShared_2696_ = v_isSharedCheck_2714_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2693_);
                            lean_dec(v___x_2692_);
                            v___x_2695_ = lean_box(0);
                            v_isShared_2696_ = v_isSharedCheck_2714_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2691_);
                        return v___x_2692_;
                    }
                } else {
                    lean_dec(v_declName_2677_);
                    v_a_2715_ = lean_ctor_get(v___x_2690_, 0);
                    v_isSharedCheck_2722_ = (!lean_is_exclusive(v___x_2690_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v___x_2717_ = v___x_2690_;
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2715_);
                        lean_dec(v___x_2690_);
                        v___x_2717_ = lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringInst_x3f_2704_ = lean_ctor_get(v_a_2691_, 10);
                lean_inc(v_ringInst_x3f_2704_);
                v_orderedRingInst_x3f_2705_ = lean_ctor_get(v_a_2691_, 11);
                lean_inc(v_orderedRingInst_x3f_2705_);
                lean_dec(v_a_2691_);
                if lean_obj_tag(v_ringInst_x3f_2704_) == 0 {
                    v___x_2711_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2712_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2711_);
                    v___y_2707_ = v___x_2712_;
                    state = 4;
                    continue;
                } else {
                    v_val_2713_ = lean_ctor_get(v_ringInst_x3f_2704_, 0);
                    lean_inc(v_val_2713_);
                    lean_dec_ref_known(v_ringInst_x3f_2704_, 1);
                    v___y_2707_ = v_val_2713_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2700_ = l_Lean_mkAppB(v_a_2693_, v___y_2698_, v___y_2699_);
                if v_isShared_2696_ == 0 {
                    lean_ctor_set(v___x_2695_, 0, v___x_2700_);
                    v___x_2702_ = v___x_2695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2702_;
            }
            4 => {
                if lean_obj_tag(v_orderedRingInst_x3f_2705_) == 0 {
                    v___x_2708_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2709_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2708_);
                    v___y_2698_ = v___y_2707_;
                    v___y_2699_ = v___x_2709_;
                    state = 2;
                    continue;
                } else {
                    v_val_2710_ = lean_ctor_get(v_orderedRingInst_x3f_2705_, 0);
                    lean_inc(v_val_2710_);
                    lean_dec_ref_known(v_orderedRingInst_x3f_2705_, 1);
                    v___y_2698_ = v___y_2707_;
                    v___y_2699_ = v_val_2710_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2718_ == 0 {
                    v___x_2720_ = v___x_2717_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
                    v___x_2720_ = v_reuseFailAlloc_2721_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix___boxed(
    mut v_declName_2723_: *mut LeanObject,
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
    mut v_a_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2736_: *mut LeanObject = core::ptr::null_mut();
    v_res_2736_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(
        v_declName_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
        v_a_2733_,
        v_a_2734_,
    );
    lean_dec(v_a_2734_);
    lean_dec_ref(v_a_2733_);
    lean_dec(v_a_2732_);
    lean_dec_ref(v_a_2731_);
    lean_dec(v_a_2730_);
    lean_dec_ref(v_a_2729_);
    lean_dec(v_a_2728_);
    lean_dec_ref(v_a_2727_);
    lean_dec(v_a_2726_);
    lean_dec(v_a_2725_);
    lean_dec(v_a_2724_);
    return v_res_2736_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(
    mut v_u_2764_: *mut LeanObject,
    mut v_v_2765_: *mut LeanObject,
    mut v_w_2766_: *mut LeanObject,
    mut v_strict_u2081_2767_: u8,
    mut v_strict_u2082_2768_: u8,
    mut v_h_u2081_2769_: *mut LeanObject,
    mut v_h_u2082_2770_: *mut LeanObject,
    mut v_a_2771_: *mut LeanObject,
    mut v_a_2772_: *mut LeanObject,
    mut v_a_2773_: *mut LeanObject,
    mut v_a_2774_: *mut LeanObject,
    mut v_a_2775_: *mut LeanObject,
    mut v_a_2776_: *mut LeanObject,
    mut v_a_2777_: *mut LeanObject,
    mut v_a_2778_: *mut LeanObject,
    mut v_a_2779_: *mut LeanObject,
    mut v_a_2780_: *mut LeanObject,
    mut v_a_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_strict_u2081_2767_ == 0 {
                    if v_strict_u2082_2768_ == 0 {
                        v___x_2787_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4;
                        v___x_2788_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(
                            v___x_2787_,
                            v_a_2771_,
                            v_a_2772_,
                            v_a_2773_,
                            v_a_2774_,
                            v_a_2775_,
                            v_a_2776_,
                            v_a_2777_,
                            v_a_2778_,
                            v_a_2779_,
                            v_a_2780_,
                            v_a_2781_,
                        );
                        if lean_obj_tag(v___x_2788_) == 0 {
                            v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
                            lean_inc(v_a_2789_);
                            lean_dec_ref_known(v___x_2788_, 1);
                            v_h_2784_ = v_a_2789_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2770_);
                            lean_dec_ref(v_h_u2081_2769_);
                            lean_dec_ref(v_w_2766_);
                            lean_dec_ref(v_v_2765_);
                            lean_dec_ref(v_u_2764_);
                            return v___x_2788_;
                        }
                    } else {
                        v___x_2790_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6;
                        v___x_2791_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2790_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if lean_obj_tag(v___x_2791_) == 0 {
                            v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
                            lean_inc(v_a_2792_);
                            lean_dec_ref_known(v___x_2791_, 1);
                            v_h_2784_ = v_a_2792_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2770_);
                            lean_dec_ref(v_h_u2081_2769_);
                            lean_dec_ref(v_w_2766_);
                            lean_dec_ref(v_v_2765_);
                            lean_dec_ref(v_u_2764_);
                            return v___x_2791_;
                        }
                    }
                } else {
                    if v_strict_u2082_2768_ == 0 {
                        v___x_2793_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8;
                        v___x_2794_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2793_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if lean_obj_tag(v___x_2794_) == 0 {
                            v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
                            lean_inc(v_a_2795_);
                            lean_dec_ref_known(v___x_2794_, 1);
                            v_h_2784_ = v_a_2795_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2770_);
                            lean_dec_ref(v_h_u2081_2769_);
                            lean_dec_ref(v_w_2766_);
                            lean_dec_ref(v_v_2765_);
                            lean_dec_ref(v_u_2764_);
                            return v___x_2794_;
                        }
                    } else {
                        v___x_2796_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10;
                        v___x_2797_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2796_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if lean_obj_tag(v___x_2797_) == 0 {
                            v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
                            lean_inc(v_a_2798_);
                            lean_dec_ref_known(v___x_2797_, 1);
                            v_h_2784_ = v_a_2798_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2770_);
                            lean_dec_ref(v_h_u2081_2769_);
                            lean_dec_ref(v_w_2766_);
                            lean_dec_ref(v_v_2765_);
                            lean_dec_ref(v_u_2764_);
                            return v___x_2797_;
                        }
                    }
                }
            }
            1 => {
                v___x_2785_ = l_Lean_mkApp5(
                    v_h_2784_,
                    v_u_2764_,
                    v_v_2765_,
                    v_w_2766_,
                    v_h_u2081_2769_,
                    v_h_u2082_2770_,
                );
                v___x_2786_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2786_, 0, v___x_2785_);
                return v___x_2786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_2799_: *mut LeanObject = *_args.add(0);
    let mut v_v_2800_: *mut LeanObject = *_args.add(1);
    let mut v_w_2801_: *mut LeanObject = *_args.add(2);
    let mut v_strict_u2081_2802_: *mut LeanObject = *_args.add(3);
    let mut v_strict_u2082_2803_: *mut LeanObject = *_args.add(4);
    let mut v_h_u2081_2804_: *mut LeanObject = *_args.add(5);
    let mut v_h_u2082_2805_: *mut LeanObject = *_args.add(6);
    let mut v_a_2806_: *mut LeanObject = *_args.add(7);
    let mut v_a_2807_: *mut LeanObject = *_args.add(8);
    let mut v_a_2808_: *mut LeanObject = *_args.add(9);
    let mut v_a_2809_: *mut LeanObject = *_args.add(10);
    let mut v_a_2810_: *mut LeanObject = *_args.add(11);
    let mut v_a_2811_: *mut LeanObject = *_args.add(12);
    let mut v_a_2812_: *mut LeanObject = *_args.add(13);
    let mut v_a_2813_: *mut LeanObject = *_args.add(14);
    let mut v_a_2814_: *mut LeanObject = *_args.add(15);
    let mut v_a_2815_: *mut LeanObject = *_args.add(16);
    let mut v_a_2816_: *mut LeanObject = *_args.add(17);
    let mut v_a_2817_: *mut LeanObject = *_args.add(18);
    let mut v_strict_u2081_boxed_2818_: u8 = 0;
    let mut v_strict_u2082_boxed_2819_: u8 = 0;
    let mut v_res_2820_: *mut LeanObject = core::ptr::null_mut();
    v_strict_u2081_boxed_2818_ = (lean_unbox(v_strict_u2081_2802_) as u8);
    v_strict_u2082_boxed_2819_ = (lean_unbox(v_strict_u2082_2803_) as u8);
    v_res_2820_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(
            v_u_2799_,
            v_v_2800_,
            v_w_2801_,
            v_strict_u2081_boxed_2818_,
            v_strict_u2082_boxed_2819_,
            v_h_u2081_2804_,
            v_h_u2082_2805_,
            v_a_2806_,
            v_a_2807_,
            v_a_2808_,
            v_a_2809_,
            v_a_2810_,
            v_a_2811_,
            v_a_2812_,
            v_a_2813_,
            v_a_2814_,
            v_a_2815_,
            v_a_2816_,
        );
    lean_dec(v_a_2816_);
    lean_dec_ref(v_a_2815_);
    lean_dec(v_a_2814_);
    lean_dec_ref(v_a_2813_);
    lean_dec(v_a_2812_);
    lean_dec_ref(v_a_2811_);
    lean_dec(v_a_2810_);
    lean_dec_ref(v_a_2809_);
    lean_dec(v_a_2808_);
    lean_dec(v_a_2807_);
    lean_dec(v_a_2806_);
    return v_res_2820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(
    mut v_xs_2821_: *mut LeanObject,
    mut v_i_2822_: *mut LeanObject,
) -> u8 {
    let mut v_size_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    v_size_2823_ = lean_ctor_get(v_xs_2821_, 2);
    v___x_2824_ = lean_nat_dec_lt(v_i_2822_, v_size_2823_);
    return v___x_2824_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(
    mut v_xs_2825_: *mut LeanObject,
    mut v_i_2826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2827_: u8 = 0;
    let mut v_r_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2827_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_2825_, v_i_2826_);
    lean_dec(v_i_2826_);
    lean_dec_ref(v_xs_2825_);
    v_r_2828_ = lean_box((v_res_2827_) as usize);
    return v_r_2828_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0()
-> *mut LeanObject {
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    v___x_2829_ = lean_unsigned_to_nat(0);
    v___x_2830_ = lean_nat_to_int(v___x_2829_);
    return v___x_2830_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(
    mut v_p_u2081_2831_: *mut LeanObject,
    mut v_p_u2082_2832_: *mut LeanObject,
    mut v_v_2833_: *mut LeanObject,
    mut v_a_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_a_2839_: *mut LeanObject,
    mut v_a_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___y_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2855_: u8 = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_2862_: u8 = 0;
    let mut v_w_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_nodes_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u8 = 0;
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_w_2846_ = lean_ctor_get(v_p_u2081_2831_, 0);
                v_k_2847_ = lean_ctor_get(v_p_u2081_2831_, 1);
                v_proof_2848_ = lean_ctor_get(v_p_u2081_2831_, 2);
                v_isSharedCheck_2907_ = (!lean_is_exclusive(v_p_u2081_2831_)) as u8;
                if v_isSharedCheck_2907_ == 0 {
                    v___x_2850_ = v_p_u2081_2831_;
                    v_isShared_2851_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_proof_2848_);
                    lean_inc(v_k_2847_);
                    lean_inc(v_w_2846_);
                    lean_dec(v_p_u2081_2831_);
                    v___x_2850_ = lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_k_2861_ = lean_ctor_get(v_p_u2082_2832_, 1);
                lean_inc_ref(v_k_2861_);
                v_strict_2862_ = lean_ctor_get_uint8(
                    v_k_2847_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_k_2847_);
                v_w_2863_ = lean_ctor_get(v_p_u2082_2832_, 0);
                lean_inc(v_w_2863_);
                v_proof_2864_ = lean_ctor_get(v_p_u2082_2832_, 2);
                lean_inc_ref(v_proof_2864_);
                lean_dec_ref(v_p_u2082_2832_);
                v_strict_2865_ = lean_ctor_get_uint8(
                    v_k_2861_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_k_2861_);
                v___x_2866_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_,
                    v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_,
                );
                if lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
                    lean_inc(v_a_2867_);
                    lean_dec_ref_known(v___x_2866_, 1);
                    v_nodes_2883_ = lean_ctor_get(v_a_2867_, 14);
                    lean_inc_ref(v_nodes_2883_);
                    lean_dec(v_a_2867_);
                    v___x_2884_ = l_Lean_instInhabitedExpr;
                    v___x_2896_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_2883_, v_w_2846_);
                    if v___x_2896_ == 0 {
                        v___x_2897_ = l_outOfBounds___redArg(v___x_2884_);
                        v___y_2892_ = v___x_2897_;
                        state = 8;
                        continue;
                    } else {
                        v___x_2898_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_2884_,
                            v_nodes_2883_,
                            v_w_2846_,
                        );
                        v___y_2892_ = v___x_2898_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_proof_2864_);
                    lean_dec(v_w_2863_);
                    lean_del_object(v___x_2850_);
                    lean_dec_ref(v_proof_2848_);
                    lean_dec(v_w_2846_);
                    v_a_2899_ = lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2906_ = (!lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2901_ = v___x_2866_;
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2899_);
                        lean_dec(v___x_2866_);
                        v___x_2901_ = lean_box(0);
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v___y_2853_);
                v___x_2856_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2856_, 0, v___y_2853_);
                lean_ctor_set_uint8(
                    v___x_2856_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_2855_,
                );
                if v_isShared_2851_ == 0 {
                    lean_ctor_set(v___x_2850_, 2, v___y_2854_);
                    lean_ctor_set(v___x_2850_, 1, v___x_2856_);
                    v___x_2858_ = v___x_2850_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_w_2846_);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2856_);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 2, v___y_2854_);
                    v___x_2858_ = v_reuseFailAlloc_2860_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2859_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2859_, 0, v___x_2858_);
                return v___x_2859_;
            }
            4 => {
                v___x_2872_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v___y_2870_, v___y_2869_, v___y_2871_, v_strict_2862_, v_strict_2865_, v_proof_2848_, v_proof_2864_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
                if lean_obj_tag(v___x_2872_) == 0 {
                    v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
                    lean_inc(v_a_2873_);
                    lean_dec_ref_known(v___x_2872_, 1);
                    v___x_2874_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    if v_strict_2862_ == 0 {
                        v___y_2853_ = v___x_2874_;
                        v___y_2854_ = v_a_2873_;
                        v___y_2855_ = v_strict_2865_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2853_ = v___x_2874_;
                        v___y_2854_ = v_a_2873_;
                        v___y_2855_ = v_strict_2862_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2850_);
                    lean_dec(v_w_2846_);
                    v_a_2875_ = lean_ctor_get(v___x_2872_, 0);
                    v_isSharedCheck_2882_ = (!lean_is_exclusive(v___x_2872_)) as u8;
                    if v_isSharedCheck_2882_ == 0 {
                        v___x_2877_ = v___x_2872_;
                        v_isShared_2878_ = v_isSharedCheck_2882_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2875_);
                        lean_dec(v___x_2872_);
                        v___x_2877_ = lean_box(0);
                        v_isShared_2878_ = v_isSharedCheck_2882_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2878_ == 0 {
                    v___x_2880_ = v___x_2877_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
                    v___x_2880_ = v_reuseFailAlloc_2881_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2880_;
            }
            7 => {
                v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_2883_, v_v_2833_);
                if v___x_2888_ == 0 {
                    lean_dec_ref(v_nodes_2883_);
                    v___x_2889_ = l_outOfBounds___redArg(v___x_2884_);
                    v___y_2869_ = v___y_2887_;
                    v___y_2870_ = v___y_2886_;
                    v___y_2871_ = v___x_2889_;
                    state = 4;
                    continue;
                } else {
                    v___x_2890_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2884_,
                        v_nodes_2883_,
                        v_v_2833_,
                    );
                    lean_dec_ref(v_nodes_2883_);
                    v___y_2869_ = v___y_2887_;
                    v___y_2870_ = v___y_2886_;
                    v___y_2871_ = v___x_2890_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_2893_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_2883_, v_w_2863_);
                if v___x_2893_ == 0 {
                    lean_dec(v_w_2863_);
                    v___x_2894_ = l_outOfBounds___redArg(v___x_2884_);
                    v___y_2886_ = v___y_2892_;
                    v___y_2887_ = v___x_2894_;
                    state = 7;
                    continue;
                } else {
                    v___x_2895_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2884_,
                        v_nodes_2883_,
                        v_w_2863_,
                    );
                    lean_dec(v_w_2863_);
                    v___y_2886_ = v___y_2892_;
                    v___y_2887_ = v___x_2895_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v_isShared_2902_ == 0 {
                    v___x_2904_ = v___x_2901_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___boxed(
    mut v_p_u2081_2908_: *mut LeanObject,
    mut v_p_u2082_2909_: *mut LeanObject,
    mut v_v_2910_: *mut LeanObject,
    mut v_a_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
    mut v_a_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2923_: *mut LeanObject = core::ptr::null_mut();
    v_res_2923_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(
            v_p_u2081_2908_,
            v_p_u2082_2909_,
            v_v_2910_,
            v_a_2911_,
            v_a_2912_,
            v_a_2913_,
            v_a_2914_,
            v_a_2915_,
            v_a_2916_,
            v_a_2917_,
            v_a_2918_,
            v_a_2919_,
            v_a_2920_,
            v_a_2921_,
        );
    lean_dec(v_a_2921_);
    lean_dec_ref(v_a_2920_);
    lean_dec(v_a_2919_);
    lean_dec_ref(v_a_2918_);
    lean_dec(v_a_2917_);
    lean_dec_ref(v_a_2916_);
    lean_dec(v_a_2915_);
    lean_dec_ref(v_a_2914_);
    lean_dec(v_a_2913_);
    lean_dec(v_a_2912_);
    lean_dec(v_a_2911_);
    lean_dec(v_v_2910_);
    return v_res_2923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3()
-> *mut LeanObject {
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    v___x_2929_ = lean_unsigned_to_nat(0);
    v___x_2930_ = l_Lean_Level_ofNat(v___x_2929_);
    return v___x_2930_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4()
-> *mut LeanObject {
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v___x_2931_ = lean_box(0);
    v___x_2932_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
    v___x_2933_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2933_, 0, v___x_2932_);
    lean_ctor_set(v___x_2933_, 1, v___x_2931_);
    return v___x_2933_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5()
-> *mut LeanObject {
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    v___x_2934_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
    v___x_2935_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2;
    v___x_2936_ = l_Lean_Expr_const___override(v___x_2935_, v___x_2934_);
    return v___x_2936_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8()
-> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = lean_box(0);
    v___x_2941_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7;
    v___x_2942_ = l_Lean_Expr_const___override(v___x_2941_, v___x_2940_);
    return v___x_2942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11()
-> *mut LeanObject {
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    v___x_2947_ = lean_box(0);
    v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10;
    v___x_2949_ = l_Lean_Expr_const___override(v___x_2948_, v___x_2947_);
    return v___x_2949_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(
    mut v_u_2974_: *mut LeanObject,
    mut v_v_2975_: *mut LeanObject,
    mut v_w_2976_: *mut LeanObject,
    mut v_k_u2081_2977_: *mut LeanObject,
    mut v_k_u2082_2978_: *mut LeanObject,
    mut v_h_u2081_2979_: *mut LeanObject,
    mut v_h_u2082_2980_: *mut LeanObject,
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
    mut v_a_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3035_: u8 = 0;
    let mut v_h_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3051_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3058_: u8 = 0;
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3034_ = lean_ctor_get(v_k_u2081_2977_, 0);
                v_strict_3035_ = lean_ctor_get_uint8(
                    v_k_u2081_2977_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3035_ == 0 {
                    v_strict_3051_ = lean_ctor_get_uint8(
                        v_k_u2082_2978_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3051_ == 0 {
                        v___x_3052_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13;
                        v___x_3053_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                            v___x_3052_,
                            v_a_2981_,
                            v_a_2982_,
                            v_a_2983_,
                            v_a_2984_,
                            v_a_2985_,
                            v_a_2986_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                            v_a_2991_,
                        );
                        if lean_obj_tag(v___x_3053_) == 0 {
                            v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
                            lean_inc(v_a_3054_);
                            lean_dec_ref_known(v___x_3053_, 1);
                            v_h_3037_ = v_a_3054_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2980_);
                            lean_dec_ref(v_h_u2081_2979_);
                            lean_dec_ref(v_w_2976_);
                            lean_dec_ref(v_v_2975_);
                            lean_dec_ref(v_u_2974_);
                            return v___x_3053_;
                        }
                    } else {
                        v___x_3055_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15;
                        v___x_3056_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                            v___x_3055_,
                            v_a_2981_,
                            v_a_2982_,
                            v_a_2983_,
                            v_a_2984_,
                            v_a_2985_,
                            v_a_2986_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                            v_a_2991_,
                        );
                        if lean_obj_tag(v___x_3056_) == 0 {
                            v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
                            lean_inc(v_a_3057_);
                            lean_dec_ref_known(v___x_3056_, 1);
                            v_h_3037_ = v_a_3057_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2980_);
                            lean_dec_ref(v_h_u2081_2979_);
                            lean_dec_ref(v_w_2976_);
                            lean_dec_ref(v_v_2975_);
                            lean_dec_ref(v_u_2974_);
                            return v___x_3056_;
                        }
                    }
                } else {
                    v_strict_3058_ = lean_ctor_get_uint8(
                        v_k_u2082_2978_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3058_ == 0 {
                        v___x_3059_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17;
                        v___x_3060_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                            v___x_3059_,
                            v_a_2981_,
                            v_a_2982_,
                            v_a_2983_,
                            v_a_2984_,
                            v_a_2985_,
                            v_a_2986_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                            v_a_2991_,
                        );
                        if lean_obj_tag(v___x_3060_) == 0 {
                            v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
                            lean_inc(v_a_3061_);
                            lean_dec_ref_known(v___x_3060_, 1);
                            v_h_3037_ = v_a_3061_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2980_);
                            lean_dec_ref(v_h_u2081_2979_);
                            lean_dec_ref(v_w_2976_);
                            lean_dec_ref(v_v_2975_);
                            lean_dec_ref(v_u_2974_);
                            return v___x_3060_;
                        }
                    } else {
                        v___x_3062_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19;
                        v___x_3063_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                            v___x_3062_,
                            v_a_2981_,
                            v_a_2982_,
                            v_a_2983_,
                            v_a_2984_,
                            v_a_2985_,
                            v_a_2986_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                            v_a_2991_,
                        );
                        if lean_obj_tag(v___x_3063_) == 0 {
                            v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
                            lean_inc(v_a_3064_);
                            lean_dec_ref_known(v___x_3063_, 1);
                            v_h_3037_ = v_a_3064_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v_h_u2082_2980_);
                            lean_dec_ref(v_h_u2081_2979_);
                            lean_dec_ref(v_w_2976_);
                            lean_dec_ref(v_v_2975_);
                            lean_dec_ref(v_u_2974_);
                            return v___x_3063_;
                        }
                    }
                }
            }
            1 => {
                v_h_2998_ = l_Lean_mkApp6(
                    v___y_2994_,
                    v_u_2974_,
                    v_v_2975_,
                    v_w_2976_,
                    v___y_2996_,
                    v___y_2995_,
                    v___y_2997_,
                );
                v___x_2999_ = l_Lean_eagerReflBoolTrue;
                v___x_3000_ =
                    l_Lean_mkApp3(v_h_2998_, v_h_u2081_2979_, v_h_u2082_2980_, v___x_2999_);
                v___x_3001_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3001_, 0, v___x_3000_);
                return v___x_3001_;
            }
            2 => {
                v___x_3007_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3008_ = lean_int_dec_le(v___x_3007_, v___y_3004_);
                if v___x_3008_ == 0 {
                    v___x_3009_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3010_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3011_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3012_ = lean_int_neg(v___y_3004_);
                    lean_dec(v___y_3004_);
                    v___x_3013_ = l_Int_toNat(v___x_3012_);
                    lean_dec(v___x_3012_);
                    v___x_3014_ = l_Lean_instToExprInt_mkNat(v___x_3013_);
                    v___x_3015_ = l_Lean_mkApp3(v___x_3009_, v___x_3010_, v___x_3011_, v___x_3014_);
                    v___y_2994_ = v___y_3003_;
                    v___y_2995_ = v___y_3006_;
                    v___y_2996_ = v___y_3005_;
                    v___y_2997_ = v___x_3015_;
                    state = 1;
                    continue;
                } else {
                    v___x_3016_ = l_Int_toNat(v___y_3004_);
                    lean_dec(v___y_3004_);
                    v___x_3017_ = l_Lean_instToExprInt_mkNat(v___x_3016_);
                    v___y_2994_ = v___y_3003_;
                    v___y_2995_ = v___y_3006_;
                    v___y_2996_ = v___y_3005_;
                    v___y_2997_ = v___x_3017_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3023_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3024_ = lean_int_dec_le(v___x_3023_, v___y_3021_);
                if v___x_3024_ == 0 {
                    v___x_3025_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3026_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3027_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3028_ = lean_int_neg(v___y_3021_);
                    v___x_3029_ = l_Int_toNat(v___x_3028_);
                    lean_dec(v___x_3028_);
                    v___x_3030_ = l_Lean_instToExprInt_mkNat(v___x_3029_);
                    v___x_3031_ = l_Lean_mkApp3(v___x_3025_, v___x_3026_, v___x_3027_, v___x_3030_);
                    v___y_3003_ = v___y_3019_;
                    v___y_3004_ = v___y_3020_;
                    v___y_3005_ = v___y_3022_;
                    v___y_3006_ = v___x_3031_;
                    state = 2;
                    continue;
                } else {
                    v___x_3032_ = l_Int_toNat(v___y_3021_);
                    v___x_3033_ = l_Lean_instToExprInt_mkNat(v___x_3032_);
                    v___y_3003_ = v___y_3019_;
                    v___y_3004_ = v___y_3020_;
                    v___y_3005_ = v___y_3022_;
                    v___y_3006_ = v___x_3033_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_k_3038_ = lean_ctor_get(v_k_u2082_2978_, 0);
                v_k_3039_ = lean_int_add(v_k_3034_, v_k_3038_);
                v___x_3040_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3041_ = lean_int_dec_le(v___x_3040_, v_k_3034_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3043_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3044_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3045_ = lean_int_neg(v_k_3034_);
                    v___x_3046_ = l_Int_toNat(v___x_3045_);
                    lean_dec(v___x_3045_);
                    v___x_3047_ = l_Lean_instToExprInt_mkNat(v___x_3046_);
                    v___x_3048_ = l_Lean_mkApp3(v___x_3042_, v___x_3043_, v___x_3044_, v___x_3047_);
                    v___y_3019_ = v_h_3037_;
                    v___y_3020_ = v_k_3039_;
                    v___y_3021_ = v_k_3038_;
                    v___y_3022_ = v___x_3048_;
                    state = 3;
                    continue;
                } else {
                    v___x_3049_ = l_Int_toNat(v_k_3034_);
                    v___x_3050_ = l_Lean_instToExprInt_mkNat(v___x_3049_);
                    v___y_3019_ = v_h_3037_;
                    v___y_3020_ = v_k_3039_;
                    v___y_3021_ = v_k_3038_;
                    v___y_3022_ = v___x_3050_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3065_: *mut LeanObject = *_args.add(0);
    let mut v_v_3066_: *mut LeanObject = *_args.add(1);
    let mut v_w_3067_: *mut LeanObject = *_args.add(2);
    let mut v_k_u2081_3068_: *mut LeanObject = *_args.add(3);
    let mut v_k_u2082_3069_: *mut LeanObject = *_args.add(4);
    let mut v_h_u2081_3070_: *mut LeanObject = *_args.add(5);
    let mut v_h_u2082_3071_: *mut LeanObject = *_args.add(6);
    let mut v_a_3072_: *mut LeanObject = *_args.add(7);
    let mut v_a_3073_: *mut LeanObject = *_args.add(8);
    let mut v_a_3074_: *mut LeanObject = *_args.add(9);
    let mut v_a_3075_: *mut LeanObject = *_args.add(10);
    let mut v_a_3076_: *mut LeanObject = *_args.add(11);
    let mut v_a_3077_: *mut LeanObject = *_args.add(12);
    let mut v_a_3078_: *mut LeanObject = *_args.add(13);
    let mut v_a_3079_: *mut LeanObject = *_args.add(14);
    let mut v_a_3080_: *mut LeanObject = *_args.add(15);
    let mut v_a_3081_: *mut LeanObject = *_args.add(16);
    let mut v_a_3082_: *mut LeanObject = *_args.add(17);
    let mut v_a_3083_: *mut LeanObject = *_args.add(18);
    let mut v_res_3084_: *mut LeanObject = core::ptr::null_mut();
    v_res_3084_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(
            v_u_3065_,
            v_v_3066_,
            v_w_3067_,
            v_k_u2081_3068_,
            v_k_u2082_3069_,
            v_h_u2081_3070_,
            v_h_u2082_3071_,
            v_a_3072_,
            v_a_3073_,
            v_a_3074_,
            v_a_3075_,
            v_a_3076_,
            v_a_3077_,
            v_a_3078_,
            v_a_3079_,
            v_a_3080_,
            v_a_3081_,
            v_a_3082_,
        );
    lean_dec(v_a_3082_);
    lean_dec_ref(v_a_3081_);
    lean_dec(v_a_3080_);
    lean_dec_ref(v_a_3079_);
    lean_dec(v_a_3078_);
    lean_dec_ref(v_a_3077_);
    lean_dec(v_a_3076_);
    lean_dec_ref(v_a_3075_);
    lean_dec(v_a_3074_);
    lean_dec(v_a_3073_);
    lean_dec(v_a_3072_);
    lean_dec_ref(v_k_u2082_3069_);
    lean_dec_ref(v_k_u2081_3068_);
    return v_res_3084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(
    mut v_p_u2081_3085_: *mut LeanObject,
    mut v_p_u2082_3086_: *mut LeanObject,
    mut v_v_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___y_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_w_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3127_: u8 = 0;
    let mut v_k_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3129_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_nodes_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3158_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3162_: u8 = 0;
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_w_3100_ = lean_ctor_get(v_p_u2081_3085_, 0);
                v_k_3101_ = lean_ctor_get(v_p_u2081_3085_, 1);
                v_proof_3102_ = lean_ctor_get(v_p_u2081_3085_, 2);
                v_isSharedCheck_3163_ = (!lean_is_exclusive(v_p_u2081_3085_)) as u8;
                if v_isSharedCheck_3163_ == 0 {
                    v___x_3104_ = v_p_u2081_3085_;
                    v_isShared_3105_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_proof_3102_);
                    lean_inc(v_k_3101_);
                    lean_inc(v_w_3100_);
                    lean_dec(v_p_u2081_3085_);
                    v___x_3104_ = lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_w_3115_ = lean_ctor_get(v_p_u2082_3086_, 0);
                lean_inc(v_w_3115_);
                v_k_3116_ = lean_ctor_get(v_p_u2082_3086_, 1);
                lean_inc_ref(v_k_3116_);
                v_proof_3117_ = lean_ctor_get(v_p_u2082_3086_, 2);
                lean_inc_ref(v_proof_3117_);
                lean_dec_ref(v_p_u2082_3086_);
                v___x_3118_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_,
                    v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_,
                );
                if lean_obj_tag(v___x_3118_) == 0 {
                    v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
                    lean_inc(v_a_3119_);
                    lean_dec_ref_known(v___x_3118_, 1);
                    v_nodes_3139_ = lean_ctor_get(v_a_3119_, 14);
                    lean_inc_ref(v_nodes_3139_);
                    lean_dec(v_a_3119_);
                    v___x_3140_ = l_Lean_instInhabitedExpr;
                    v___x_3152_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_3139_, v_w_3100_);
                    if v___x_3152_ == 0 {
                        v___x_3153_ = l_outOfBounds___redArg(v___x_3140_);
                        v___y_3148_ = v___x_3153_;
                        state = 8;
                        continue;
                    } else {
                        v___x_3154_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_3140_,
                            v_nodes_3139_,
                            v_w_3100_,
                        );
                        v___y_3148_ = v___x_3154_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_proof_3117_);
                    lean_dec_ref(v_k_3116_);
                    lean_dec(v_w_3115_);
                    lean_del_object(v___x_3104_);
                    lean_dec_ref(v_proof_3102_);
                    lean_dec_ref(v_k_3101_);
                    lean_dec(v_w_3100_);
                    v_a_3155_ = lean_ctor_get(v___x_3118_, 0);
                    v_isSharedCheck_3162_ = (!lean_is_exclusive(v___x_3118_)) as u8;
                    if v_isSharedCheck_3162_ == 0 {
                        v___x_3157_ = v___x_3118_;
                        v_isShared_3158_ = v_isSharedCheck_3162_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3155_);
                        lean_dec(v___x_3118_);
                        v___x_3157_ = lean_box(0);
                        v_isShared_3158_ = v_isSharedCheck_3162_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3110_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3110_, 0, v___y_3107_);
                lean_ctor_set_uint8(
                    v___x_3110_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_3109_,
                );
                if v_isShared_3105_ == 0 {
                    lean_ctor_set(v___x_3104_, 2, v___y_3108_);
                    lean_ctor_set(v___x_3104_, 1, v___x_3110_);
                    v___x_3112_ = v___x_3104_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_w_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3110_);
                    lean_ctor_set(v_reuseFailAlloc_3114_, 2, v___y_3108_);
                    v___x_3112_ = v_reuseFailAlloc_3114_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3113_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3113_, 0, v___x_3112_);
                return v___x_3113_;
            }
            4 => {
                v___x_3124_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v___y_3121_, v___y_3122_, v___y_3123_, v_k_3101_, v_k_3116_, v_proof_3102_, v_proof_3117_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
                if lean_obj_tag(v___x_3124_) == 0 {
                    v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
                    lean_inc(v_a_3125_);
                    lean_dec_ref_known(v___x_3124_, 1);
                    v_k_3126_ = lean_ctor_get(v_k_3101_, 0);
                    lean_inc(v_k_3126_);
                    v_strict_3127_ = lean_ctor_get_uint8(
                        v_k_3101_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref(v_k_3101_);
                    v_k_3128_ = lean_ctor_get(v_k_3116_, 0);
                    lean_inc(v_k_3128_);
                    v_strict_3129_ = lean_ctor_get_uint8(
                        v_k_3116_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref(v_k_3116_);
                    v___x_3130_ = lean_int_add(v_k_3126_, v_k_3128_);
                    lean_dec(v_k_3128_);
                    lean_dec(v_k_3126_);
                    if v_strict_3127_ == 0 {
                        v___y_3107_ = v___x_3130_;
                        v___y_3108_ = v_a_3125_;
                        v___y_3109_ = v_strict_3129_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3107_ = v___x_3130_;
                        v___y_3108_ = v_a_3125_;
                        v___y_3109_ = v_strict_3127_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_3116_);
                    lean_del_object(v___x_3104_);
                    lean_dec_ref(v_k_3101_);
                    lean_dec(v_w_3100_);
                    v_a_3131_ = lean_ctor_get(v___x_3124_, 0);
                    v_isSharedCheck_3138_ = (!lean_is_exclusive(v___x_3124_)) as u8;
                    if v_isSharedCheck_3138_ == 0 {
                        v___x_3133_ = v___x_3124_;
                        v_isShared_3134_ = v_isSharedCheck_3138_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3131_);
                        lean_dec(v___x_3124_);
                        v___x_3133_ = lean_box(0);
                        v_isShared_3134_ = v_isSharedCheck_3138_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3134_ == 0 {
                    v___x_3136_ = v___x_3133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
                    v___x_3136_ = v_reuseFailAlloc_3137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3136_;
            }
            7 => {
                v___x_3144_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_3139_, v_v_3087_);
                if v___x_3144_ == 0 {
                    lean_dec_ref(v_nodes_3139_);
                    v___x_3145_ = l_outOfBounds___redArg(v___x_3140_);
                    v___y_3121_ = v___y_3142_;
                    v___y_3122_ = v___y_3143_;
                    v___y_3123_ = v___x_3145_;
                    state = 4;
                    continue;
                } else {
                    v___x_3146_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3140_,
                        v_nodes_3139_,
                        v_v_3087_,
                    );
                    lean_dec_ref(v_nodes_3139_);
                    v___y_3121_ = v___y_3142_;
                    v___y_3122_ = v___y_3143_;
                    v___y_3123_ = v___x_3146_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_3149_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_nodes_3139_, v_w_3115_);
                if v___x_3149_ == 0 {
                    lean_dec(v_w_3115_);
                    v___x_3150_ = l_outOfBounds___redArg(v___x_3140_);
                    v___y_3142_ = v___y_3148_;
                    v___y_3143_ = v___x_3150_;
                    state = 7;
                    continue;
                } else {
                    v___x_3151_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3140_,
                        v_nodes_3139_,
                        v_w_3115_,
                    );
                    lean_dec(v_w_3115_);
                    v___y_3142_ = v___y_3148_;
                    v___y_3143_ = v___x_3151_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v_isShared_3158_ == 0 {
                    v___x_3160_ = v___x_3157_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
                    v___x_3160_ = v_reuseFailAlloc_3161_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset___boxed(
    mut v_p_u2081_3164_: *mut LeanObject,
    mut v_p_u2082_3165_: *mut LeanObject,
    mut v_v_3166_: *mut LeanObject,
    mut v_a_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
    mut v_a_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_res_3179_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(
            v_p_u2081_3164_,
            v_p_u2082_3165_,
            v_v_3166_,
            v_a_3167_,
            v_a_3168_,
            v_a_3169_,
            v_a_3170_,
            v_a_3171_,
            v_a_3172_,
            v_a_3173_,
            v_a_3174_,
            v_a_3175_,
            v_a_3176_,
            v_a_3177_,
        );
    lean_dec(v_a_3177_);
    lean_dec_ref(v_a_3176_);
    lean_dec(v_a_3175_);
    lean_dec_ref(v_a_3174_);
    lean_dec(v_a_3173_);
    lean_dec_ref(v_a_3172_);
    lean_dec(v_a_3171_);
    lean_dec_ref(v_a_3170_);
    lean_dec(v_a_3169_);
    lean_dec(v_a_3168_);
    lean_dec(v_a_3167_);
    lean_dec(v_v_3166_);
    return v_res_3179_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkTrans(
    mut v_p_u2081_3180_: *mut LeanObject,
    mut v_p_u2082_3181_: *mut LeanObject,
    mut v_v_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
    mut v_a_3189_: *mut LeanObject,
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
    mut v_a_3192_: *mut LeanObject,
    mut v_a_3193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3195_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_,
                    v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_,
                );
                if lean_obj_tag(v___x_3195_) == 0 {
                    v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
                    lean_inc(v_a_3196_);
                    lean_dec_ref_known(v___x_3195_, 1);
                    v___x_3197_ = (lean_unbox(v_a_3196_) as u8);
                    lean_dec(v_a_3196_);
                    if v___x_3197_ == 0 {
                        v___x_3198_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_3180_, v_p_u2082_3181_, v_v_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
                        return v___x_3198_;
                    } else {
                        v___x_3199_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_3180_, v_p_u2082_3181_, v_v_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
                        return v___x_3199_;
                    }
                } else {
                    lean_dec_ref(v_p_u2082_3181_);
                    lean_dec_ref(v_p_u2081_3180_);
                    v_a_3200_ = lean_ctor_get(v___x_3195_, 0);
                    v_isSharedCheck_3207_ = (!lean_is_exclusive(v___x_3195_)) as u8;
                    if v_isSharedCheck_3207_ == 0 {
                        v___x_3202_ = v___x_3195_;
                        v_isShared_3203_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3200_);
                        lean_dec(v___x_3195_);
                        v___x_3202_ = lean_box(0);
                        v_isShared_3203_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3203_ == 0 {
                    v___x_3205_ = v___x_3202_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
                    v___x_3205_ = v_reuseFailAlloc_3206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkTrans___boxed(
    mut v_p_u2081_3208_: *mut LeanObject,
    mut v_p_u2082_3209_: *mut LeanObject,
    mut v_v_3210_: *mut LeanObject,
    mut v_a_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
    mut v_a_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
    mut v_a_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Meta_Grind_Order_mkTrans(
        v_p_u2081_3208_,
        v_p_u2082_3209_,
        v_v_3210_,
        v_a_3211_,
        v_a_3212_,
        v_a_3213_,
        v_a_3214_,
        v_a_3215_,
        v_a_3216_,
        v_a_3217_,
        v_a_3218_,
        v_a_3219_,
        v_a_3220_,
        v_a_3221_,
    );
    lean_dec(v_a_3221_);
    lean_dec_ref(v_a_3220_);
    lean_dec(v_a_3219_);
    lean_dec_ref(v_a_3218_);
    lean_dec(v_a_3217_);
    lean_dec_ref(v_a_3216_);
    lean_dec(v_a_3215_);
    lean_dec_ref(v_a_3214_);
    lean_dec(v_a_3213_);
    lean_dec(v_a_3212_);
    lean_dec(v_a_3211_);
    lean_dec(v_v_3210_);
    return v_res_3223_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    v___x_3224_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3224_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(
    mut v_msg_3225_: *mut LeanObject,
    mut v___y_3226_: *mut LeanObject,
    mut v___y_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910__overap_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    v___x_3238_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
    v___f_3239_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3239_, 0, v___x_3238_);
    v___x_1910__overap_3240_ = lean_panic_fn_borrowed(v___f_3239_, v_msg_3225_);
    lean_dec_ref(v___f_3239_);
    lean_inc(v___y_3236_);
    lean_inc_ref(v___y_3235_);
    lean_inc(v___y_3234_);
    lean_inc_ref(v___y_3233_);
    lean_inc(v___y_3232_);
    lean_inc_ref(v___y_3231_);
    lean_inc(v___y_3230_);
    lean_inc_ref(v___y_3229_);
    lean_inc(v___y_3228_);
    lean_inc(v___y_3227_);
    lean_inc(v___y_3226_);
    v___x_3241_ = lean_apply_12(
        v___x_1910__overap_3240_,
        v___y_3226_,
        v___y_3227_,
        v___y_3228_,
        v___y_3229_,
        v___y_3230_,
        v___y_3231_,
        v___y_3232_,
        v___y_3233_,
        v___y_3234_,
        v___y_3235_,
        v___y_3236_,
        lean_box(0),
    );
    return v___x_3241_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(
    mut v_msg_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
    mut v___y_3244_: *mut LeanObject,
    mut v___y_3245_: *mut LeanObject,
    mut v___y_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3255_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
    lean_dec(v___y_3253_);
    lean_dec_ref(v___y_3252_);
    lean_dec(v___y_3251_);
    lean_dec_ref(v___y_3250_);
    lean_dec(v___y_3249_);
    lean_dec_ref(v___y_3248_);
    lean_dec(v___y_3247_);
    lean_dec_ref(v___y_3246_);
    lean_dec(v___y_3245_);
    lean_dec(v___y_3244_);
    lean_dec(v___y_3243_);
    return v_res_3255_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3()
-> *mut LeanObject {
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2;
    v___x_3260_ = lean_unsigned_to_nat(4);
    v___x_3261_ = lean_unsigned_to_nat(133);
    v___x_3262_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1;
    v___x_3263_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0;
    v___x_3264_ = l_mkPanicMessageWithDecl(
        v___x_3263_,
        v___x_3262_,
        v___x_3261_,
        v___x_3260_,
        v___x_3259_,
    );
    return v___x_3264_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(
    mut v_u_3271_: *mut LeanObject,
    mut v_v_3272_: *mut LeanObject,
    mut v_k_3273_: *mut LeanObject,
    mut v_huv_3274_: *mut LeanObject,
    mut v_k_x27_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
    mut v_a_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: *mut LeanObject,
    mut v_a_3283_: *mut LeanObject,
    mut v_a_3284_: *mut LeanObject,
    mut v_a_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3291_: u8 = 0;
    let mut v_strict_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_3291_ = lean_ctor_get_uint8(
                    v_k_3273_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_strict_3292_ = lean_ctor_get_uint8(
                    v_k_x27_3275_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3291_ == 0 {
                    if v_strict_3292_ == 0 {
                        lean_dec_ref(v_v_3272_);
                        lean_dec_ref(v_u_3271_);
                        v___x_3305_ = l_Lean_Meta_mkEqTrue(
                            v_huv_3274_,
                            v_a_3283_,
                            v_a_3284_,
                            v_a_3285_,
                            v_a_3286_,
                        );
                        return v___x_3305_;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    if v_strict_3292_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_v_3272_);
                        lean_dec_ref(v_u_3271_);
                        v___x_3306_ = l_Lean_Meta_mkEqTrue(
                            v_huv_3274_,
                            v_a_3283_,
                            v_a_3284_,
                            v_a_3285_,
                            v_a_3286_,
                        );
                        return v___x_3306_;
                    }
                }
            }
            1 => {
                v___x_3289_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
                v___x_3290_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_3289_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
                return v___x_3290_;
            }
            2 => {
                if v_strict_3291_ == 0 {
                    lean_dec_ref(v_huv_3274_);
                    lean_dec_ref(v_v_3272_);
                    lean_dec_ref(v_u_3271_);
                    state = 1;
                    continue;
                } else {
                    if v_strict_3292_ == 0 {
                        v___x_3294_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5;
                        v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_3294_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
                        if lean_obj_tag(v___x_3295_) == 0 {
                            v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
                            v_isSharedCheck_3304_ = (!lean_is_exclusive(v___x_3295_)) as u8;
                            if v_isSharedCheck_3304_ == 0 {
                                v___x_3298_ = v___x_3295_;
                                v_isShared_3299_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3296_);
                                lean_dec(v___x_3295_);
                                v___x_3298_ = lean_box(0);
                                v_isShared_3299_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_huv_3274_);
                            lean_dec_ref(v_v_3272_);
                            lean_dec_ref(v_u_3271_);
                            return v___x_3295_;
                        }
                    } else {
                        lean_dec_ref(v_huv_3274_);
                        lean_dec_ref(v_v_3272_);
                        lean_dec_ref(v_u_3271_);
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3300_ = l_Lean_mkApp3(v_a_3296_, v_u_3271_, v_v_3272_, v_huv_3274_);
                if v_isShared_3299_ == 0 {
                    lean_ctor_set(v___x_3298_, 0, v___x_3300_);
                    v___x_3302_ = v___x_3298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3307_: *mut LeanObject = *_args.add(0);
    let mut v_v_3308_: *mut LeanObject = *_args.add(1);
    let mut v_k_3309_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3310_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3311_: *mut LeanObject = *_args.add(4);
    let mut v_a_3312_: *mut LeanObject = *_args.add(5);
    let mut v_a_3313_: *mut LeanObject = *_args.add(6);
    let mut v_a_3314_: *mut LeanObject = *_args.add(7);
    let mut v_a_3315_: *mut LeanObject = *_args.add(8);
    let mut v_a_3316_: *mut LeanObject = *_args.add(9);
    let mut v_a_3317_: *mut LeanObject = *_args.add(10);
    let mut v_a_3318_: *mut LeanObject = *_args.add(11);
    let mut v_a_3319_: *mut LeanObject = *_args.add(12);
    let mut v_a_3320_: *mut LeanObject = *_args.add(13);
    let mut v_a_3321_: *mut LeanObject = *_args.add(14);
    let mut v_a_3322_: *mut LeanObject = *_args.add(15);
    let mut v_a_3323_: *mut LeanObject = *_args.add(16);
    let mut v_res_3324_: *mut LeanObject = core::ptr::null_mut();
    v_res_3324_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_3307_, v_v_3308_, v_k_3309_, v_huv_3310_, v_k_x27_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
    lean_dec(v_a_3322_);
    lean_dec_ref(v_a_3321_);
    lean_dec(v_a_3320_);
    lean_dec_ref(v_a_3319_);
    lean_dec(v_a_3318_);
    lean_dec_ref(v_a_3317_);
    lean_dec(v_a_3316_);
    lean_dec_ref(v_a_3315_);
    lean_dec(v_a_3314_);
    lean_dec(v_a_3313_);
    lean_dec(v_a_3312_);
    lean_dec_ref(v_k_x27_3311_);
    lean_dec_ref(v_k_3309_);
    return v_res_3324_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(
    mut v_u_3349_: *mut LeanObject,
    mut v_v_3350_: *mut LeanObject,
    mut v_k_3351_: *mut LeanObject,
    mut v_huv_3352_: *mut LeanObject,
    mut v_k_x27_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
    mut v_a_3359_: *mut LeanObject,
    mut v_a_3360_: *mut LeanObject,
    mut v_a_3361_: *mut LeanObject,
    mut v_a_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3374_: u8 = 0;
    let mut v___y_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3405_: u8 = 0;
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3408_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3373_ = lean_ctor_get(v_k_x27_3353_, 0);
                v_strict_3374_ = lean_ctor_get_uint8(
                    v_k_x27_3353_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3374_ == 0 {
                    v_strict_3405_ = lean_ctor_get_uint8(
                        v_k_3351_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3405_ == 0 {
                        v___x_3406_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1;
                        v___y_3390_ = v___x_3406_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3407_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3;
                        v___y_3390_ = v___x_3407_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_strict_3408_ = lean_ctor_get_uint8(
                        v_k_3351_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3408_ == 0 {
                        v___x_3409_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5;
                        v___y_3390_ = v___x_3409_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3410_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7;
                        v___y_3390_ = v___x_3410_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3370_ = l_Lean_eagerReflBoolTrue;
                v___x_3371_ = l_Lean_mkApp6(
                    v___y_3367_,
                    v_u_3349_,
                    v_v_3350_,
                    v___y_3368_,
                    v___y_3369_,
                    v___x_3370_,
                    v_huv_3352_,
                );
                v___x_3372_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3372_, 0, v___x_3371_);
                return v___x_3372_;
            }
            2 => {
                v___x_3378_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3379_ = lean_int_dec_le(v___x_3378_, v_k_3373_);
                if v___x_3379_ == 0 {
                    v___x_3380_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3381_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3382_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3383_ = lean_int_neg(v_k_3373_);
                    v___x_3384_ = l_Int_toNat(v___x_3383_);
                    lean_dec(v___x_3383_);
                    v___x_3385_ = l_Lean_instToExprInt_mkNat(v___x_3384_);
                    v___x_3386_ = l_Lean_mkApp3(v___x_3380_, v___x_3381_, v___x_3382_, v___x_3385_);
                    v___y_3367_ = v___y_3376_;
                    v___y_3368_ = v___y_3377_;
                    v___y_3369_ = v___x_3386_;
                    state = 1;
                    continue;
                } else {
                    v___x_3387_ = l_Int_toNat(v_k_3373_);
                    v___x_3388_ = l_Lean_instToExprInt_mkNat(v___x_3387_);
                    v___y_3367_ = v___y_3376_;
                    v___y_3368_ = v___y_3377_;
                    v___y_3369_ = v___x_3388_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_3390_);
                v___x_3391_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_3390_,
                    v_a_3354_,
                    v_a_3355_,
                    v_a_3356_,
                    v_a_3357_,
                    v_a_3358_,
                    v_a_3359_,
                    v_a_3360_,
                    v_a_3361_,
                    v_a_3362_,
                    v_a_3363_,
                    v_a_3364_,
                );
                if lean_obj_tag(v___x_3391_) == 0 {
                    v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
                    lean_inc(v_a_3392_);
                    lean_dec_ref_known(v___x_3391_, 1);
                    v_k_3393_ = lean_ctor_get(v_k_3351_, 0);
                    v___x_3394_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3395_ = lean_int_dec_le(v___x_3394_, v_k_3393_);
                    if v___x_3395_ == 0 {
                        v___x_3396_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3397_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3398_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3399_ = lean_int_neg(v_k_3393_);
                        v___x_3400_ = l_Int_toNat(v___x_3399_);
                        lean_dec(v___x_3399_);
                        v___x_3401_ = l_Lean_instToExprInt_mkNat(v___x_3400_);
                        v___x_3402_ =
                            l_Lean_mkApp3(v___x_3396_, v___x_3397_, v___x_3398_, v___x_3401_);
                        v___y_3376_ = v_a_3392_;
                        v___y_3377_ = v___x_3402_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3403_ = l_Int_toNat(v_k_3393_);
                        v___x_3404_ = l_Lean_instToExprInt_mkNat(v___x_3403_);
                        v___y_3376_ = v_a_3392_;
                        v___y_3377_ = v___x_3404_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_huv_3352_);
                    lean_dec_ref(v_v_3350_);
                    lean_dec_ref(v_u_3349_);
                    return v___x_3391_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3411_: *mut LeanObject = *_args.add(0);
    let mut v_v_3412_: *mut LeanObject = *_args.add(1);
    let mut v_k_3413_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3414_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3415_: *mut LeanObject = *_args.add(4);
    let mut v_a_3416_: *mut LeanObject = *_args.add(5);
    let mut v_a_3417_: *mut LeanObject = *_args.add(6);
    let mut v_a_3418_: *mut LeanObject = *_args.add(7);
    let mut v_a_3419_: *mut LeanObject = *_args.add(8);
    let mut v_a_3420_: *mut LeanObject = *_args.add(9);
    let mut v_a_3421_: *mut LeanObject = *_args.add(10);
    let mut v_a_3422_: *mut LeanObject = *_args.add(11);
    let mut v_a_3423_: *mut LeanObject = *_args.add(12);
    let mut v_a_3424_: *mut LeanObject = *_args.add(13);
    let mut v_a_3425_: *mut LeanObject = *_args.add(14);
    let mut v_a_3426_: *mut LeanObject = *_args.add(15);
    let mut v_a_3427_: *mut LeanObject = *_args.add(16);
    let mut v_res_3428_: *mut LeanObject = core::ptr::null_mut();
    v_res_3428_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_3411_, v_v_3412_, v_k_3413_, v_huv_3414_, v_k_x27_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
    lean_dec(v_a_3426_);
    lean_dec_ref(v_a_3425_);
    lean_dec(v_a_3424_);
    lean_dec_ref(v_a_3423_);
    lean_dec(v_a_3422_);
    lean_dec_ref(v_a_3421_);
    lean_dec(v_a_3420_);
    lean_dec_ref(v_a_3419_);
    lean_dec(v_a_3418_);
    lean_dec(v_a_3417_);
    lean_dec(v_a_3416_);
    lean_dec_ref(v_k_x27_3415_);
    lean_dec_ref(v_k_3413_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(
    mut v_u_3429_: *mut LeanObject,
    mut v_v_3430_: *mut LeanObject,
    mut v_k_3431_: *mut LeanObject,
    mut v_huv_3432_: *mut LeanObject,
    mut v_k_x27_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
    mut v_a_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
    mut v_a_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3446_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_,
                    v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_,
                );
                if lean_obj_tag(v___x_3446_) == 0 {
                    v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
                    lean_inc(v_a_3447_);
                    lean_dec_ref_known(v___x_3446_, 1);
                    v___x_3448_ = (lean_unbox(v_a_3447_) as u8);
                    lean_dec(v_a_3447_);
                    if v___x_3448_ == 0 {
                        v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_3429_, v_v_3430_, v_k_3431_, v_huv_3432_, v_k_x27_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3449_;
                    } else {
                        v___x_3450_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_3429_, v_v_3430_, v_k_3431_, v_huv_3432_, v_k_x27_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3450_;
                    }
                } else {
                    lean_dec_ref(v_huv_3432_);
                    lean_dec_ref(v_v_3430_);
                    lean_dec_ref(v_u_3429_);
                    v_a_3451_ = lean_ctor_get(v___x_3446_, 0);
                    v_isSharedCheck_3458_ = (!lean_is_exclusive(v___x_3446_)) as u8;
                    if v_isSharedCheck_3458_ == 0 {
                        v___x_3453_ = v___x_3446_;
                        v_isShared_3454_ = v_isSharedCheck_3458_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3451_);
                        lean_dec(v___x_3446_);
                        v___x_3453_ = lean_box(0);
                        v_isShared_3454_ = v_isSharedCheck_3458_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3454_ == 0 {
                    v___x_3456_ = v___x_3453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
                    v___x_3456_ = v_reuseFailAlloc_3457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3459_: *mut LeanObject = *_args.add(0);
    let mut v_v_3460_: *mut LeanObject = *_args.add(1);
    let mut v_k_3461_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3462_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3463_: *mut LeanObject = *_args.add(4);
    let mut v_a_3464_: *mut LeanObject = *_args.add(5);
    let mut v_a_3465_: *mut LeanObject = *_args.add(6);
    let mut v_a_3466_: *mut LeanObject = *_args.add(7);
    let mut v_a_3467_: *mut LeanObject = *_args.add(8);
    let mut v_a_3468_: *mut LeanObject = *_args.add(9);
    let mut v_a_3469_: *mut LeanObject = *_args.add(10);
    let mut v_a_3470_: *mut LeanObject = *_args.add(11);
    let mut v_a_3471_: *mut LeanObject = *_args.add(12);
    let mut v_a_3472_: *mut LeanObject = *_args.add(13);
    let mut v_a_3473_: *mut LeanObject = *_args.add(14);
    let mut v_a_3474_: *mut LeanObject = *_args.add(15);
    let mut v_a_3475_: *mut LeanObject = *_args.add(16);
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(
        v_u_3459_,
        v_v_3460_,
        v_k_3461_,
        v_huv_3462_,
        v_k_x27_3463_,
        v_a_3464_,
        v_a_3465_,
        v_a_3466_,
        v_a_3467_,
        v_a_3468_,
        v_a_3469_,
        v_a_3470_,
        v_a_3471_,
        v_a_3472_,
        v_a_3473_,
        v_a_3474_,
    );
    lean_dec(v_a_3474_);
    lean_dec_ref(v_a_3473_);
    lean_dec(v_a_3472_);
    lean_dec_ref(v_a_3471_);
    lean_dec(v_a_3470_);
    lean_dec_ref(v_a_3469_);
    lean_dec(v_a_3468_);
    lean_dec_ref(v_a_3467_);
    lean_dec(v_a_3466_);
    lean_dec(v_a_3465_);
    lean_dec(v_a_3464_);
    lean_dec_ref(v_k_x27_3463_);
    lean_dec_ref(v_k_3461_);
    return v_res_3476_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(
    mut v_u_3489_: *mut LeanObject,
    mut v_k_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3510_: u8 = 0;
    let mut v___y_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3509_ = lean_ctor_get(v_k_3490_, 0);
                v_strict_3510_ = lean_ctor_get_uint8(
                    v_k_3490_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3510_ == 0 {
                    v___x_3526_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1;
                    v___y_3512_ = v___x_3526_;
                    state = 2;
                    continue;
                } else {
                    v___x_3527_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3;
                    v___y_3512_ = v___x_3527_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3506_ = l_Lean_eagerReflBoolTrue;
                v___x_3507_ = l_Lean_mkApp3(v___y_3504_, v_u_3489_, v___y_3505_, v___x_3506_);
                v___x_3508_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3508_, 0, v___x_3507_);
                return v___x_3508_;
            }
            2 => {
                lean_inc(v___y_3512_);
                v___x_3513_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_3512_,
                    v_a_3491_,
                    v_a_3492_,
                    v_a_3493_,
                    v_a_3494_,
                    v_a_3495_,
                    v_a_3496_,
                    v_a_3497_,
                    v_a_3498_,
                    v_a_3499_,
                    v_a_3500_,
                    v_a_3501_,
                );
                if lean_obj_tag(v___x_3513_) == 0 {
                    v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
                    lean_inc(v_a_3514_);
                    lean_dec_ref_known(v___x_3513_, 1);
                    v___x_3515_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3516_ = lean_int_dec_le(v___x_3515_, v_k_3509_);
                    if v___x_3516_ == 0 {
                        v___x_3517_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3518_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3519_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3520_ = lean_int_neg(v_k_3509_);
                        v___x_3521_ = l_Int_toNat(v___x_3520_);
                        lean_dec(v___x_3520_);
                        v___x_3522_ = l_Lean_instToExprInt_mkNat(v___x_3521_);
                        v___x_3523_ =
                            l_Lean_mkApp3(v___x_3517_, v___x_3518_, v___x_3519_, v___x_3522_);
                        v___y_3504_ = v_a_3514_;
                        v___y_3505_ = v___x_3523_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3524_ = l_Int_toNat(v_k_3509_);
                        v___x_3525_ = l_Lean_instToExprInt_mkNat(v___x_3524_);
                        v___y_3504_ = v_a_3514_;
                        v___y_3505_ = v___x_3525_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_3489_);
                    return v___x_3513_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(
    mut v_u_3528_: *mut LeanObject,
    mut v_k_3529_: *mut LeanObject,
    mut v_a_3530_: *mut LeanObject,
    mut v_a_3531_: *mut LeanObject,
    mut v_a_3532_: *mut LeanObject,
    mut v_a_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
    mut v_a_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3542_: *mut LeanObject = core::ptr::null_mut();
    v_res_3542_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_3528_, v_k_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
    lean_dec(v_a_3540_);
    lean_dec_ref(v_a_3539_);
    lean_dec(v_a_3538_);
    lean_dec_ref(v_a_3537_);
    lean_dec(v_a_3536_);
    lean_dec_ref(v_a_3535_);
    lean_dec(v_a_3534_);
    lean_dec_ref(v_a_3533_);
    lean_dec(v_a_3532_);
    lean_dec(v_a_3531_);
    lean_dec(v_a_3530_);
    lean_dec_ref(v_k_3529_);
    return v_res_3542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(
    mut v_u_3549_: *mut LeanObject,
    mut v_a_3550_: *mut LeanObject,
    mut v_a_3551_: *mut LeanObject,
    mut v_a_3552_: *mut LeanObject,
    mut v_a_3553_: *mut LeanObject,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
    mut v_a_3556_: *mut LeanObject,
    mut v_a_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
    mut v_a_3559_: *mut LeanObject,
    mut v_a_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3562_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1;
                v___x_3563_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(
                    v___x_3562_,
                    v_a_3550_,
                    v_a_3551_,
                    v_a_3552_,
                    v_a_3553_,
                    v_a_3554_,
                    v_a_3555_,
                    v_a_3556_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if lean_obj_tag(v___x_3563_) == 0 {
                    v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
                    v_isSharedCheck_3572_ = (!lean_is_exclusive(v___x_3563_)) as u8;
                    if v_isSharedCheck_3572_ == 0 {
                        v___x_3566_ = v___x_3563_;
                        v_isShared_3567_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3564_);
                        lean_dec(v___x_3563_);
                        v___x_3566_ = lean_box(0);
                        v_isShared_3567_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_3549_);
                    return v___x_3563_;
                }
            }
            1 => {
                v___x_3568_ = l_Lean_Expr_app___override(v_a_3564_, v_u_3549_);
                if v_isShared_3567_ == 0 {
                    lean_ctor_set(v___x_3566_, 0, v___x_3568_);
                    v___x_3570_ = v___x_3566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
                    v___x_3570_ = v_reuseFailAlloc_3571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___boxed(
    mut v_u_3573_: *mut LeanObject,
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
    mut v_a_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3586_: *mut LeanObject = core::ptr::null_mut();
    v_res_3586_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
    lean_dec(v_a_3584_);
    lean_dec_ref(v_a_3583_);
    lean_dec(v_a_3582_);
    lean_dec_ref(v_a_3581_);
    lean_dec(v_a_3580_);
    lean_dec_ref(v_a_3579_);
    lean_dec(v_a_3578_);
    lean_dec_ref(v_a_3577_);
    lean_dec(v_a_3576_);
    lean_dec(v_a_3575_);
    lean_dec(v_a_3574_);
    return v_res_3586_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2()
-> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1;
    v___x_3590_ = lean_unsigned_to_nat(4);
    v___x_3591_ = lean_unsigned_to_nat(175);
    v___x_3592_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0;
    v___x_3593_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0;
    v___x_3594_ = l_mkPanicMessageWithDecl(
        v___x_3593_,
        v___x_3592_,
        v___x_3591_,
        v___x_3590_,
        v___x_3589_,
    );
    return v___x_3594_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(
    mut v_u_3595_: *mut LeanObject,
    mut v_k_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
    mut v_a_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v_strict_3612_: u8 = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3609_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_,
                    v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_,
                );
                if lean_obj_tag(v___x_3609_) == 0 {
                    v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
                    lean_inc(v_a_3610_);
                    lean_dec_ref_known(v___x_3609_, 1);
                    v___x_3611_ = (lean_unbox(v_a_3610_) as u8);
                    lean_dec(v_a_3610_);
                    if v___x_3611_ == 0 {
                        v_strict_3612_ = lean_ctor_get_uint8(
                            v_k_3596_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_strict_3612_ == 0 {
                            v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_3595_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                            return v___x_3613_;
                        } else {
                            lean_dec_ref(v_u_3595_);
                            v___x_3614_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once), _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
                            v___x_3615_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_3614_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                            return v___x_3615_;
                        }
                    } else {
                        v___x_3616_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_3595_, v_k_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                        return v___x_3616_;
                    }
                } else {
                    lean_dec_ref(v_u_3595_);
                    v_a_3617_ = lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3624_ = (!lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3619_ = v___x_3609_;
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3617_);
                        lean_dec(v___x_3609_);
                        v___x_3619_ = lean_box(0);
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3620_ == 0 {
                    v___x_3622_ = v___x_3619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___boxed(
    mut v_u_3625_: *mut LeanObject,
    mut v_k_3626_: *mut LeanObject,
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
    mut v_a_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3639_: *mut LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(
        v_u_3625_, v_k_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_,
        v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_,
    );
    lean_dec(v_a_3637_);
    lean_dec_ref(v_a_3636_);
    lean_dec(v_a_3635_);
    lean_dec_ref(v_a_3634_);
    lean_dec(v_a_3633_);
    lean_dec_ref(v_a_3632_);
    lean_dec(v_a_3631_);
    lean_dec_ref(v_a_3630_);
    lean_dec(v_a_3629_);
    lean_dec(v_a_3628_);
    lean_dec(v_a_3627_);
    lean_dec_ref(v_k_3626_);
    return v_res_3639_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(
    mut v_msg_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    v___x_3641_ = lean_box(0);
    v___x_3642_ = lean_panic_fn_borrowed(v___x_3641_, v_msg_3640_);
    return v___x_3642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2()
-> *mut LeanObject {
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    v___x_3645_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1;
    v___x_3646_ = lean_unsigned_to_nat(22);
    v___x_3647_ = lean_unsigned_to_nat(183);
    v___x_3648_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0;
    v___x_3649_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0;
    v___x_3650_ = l_mkPanicMessageWithDecl(
        v___x_3649_,
        v___x_3648_,
        v___x_3647_,
        v___x_3646_,
        v___x_3645_,
    );
    return v___x_3650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(
    mut v_u_3669_: *mut LeanObject,
    mut v_v_3670_: *mut LeanObject,
    mut v_k_3671_: *mut LeanObject,
    mut v_huv_3672_: *mut LeanObject,
    mut v_k_x27_3673_: *mut LeanObject,
    mut v_a_3674_: *mut LeanObject,
    mut v_a_3675_: *mut LeanObject,
    mut v_a_3676_: *mut LeanObject,
    mut v_a_3677_: *mut LeanObject,
    mut v_a_3678_: *mut LeanObject,
    mut v_a_3679_: *mut LeanObject,
    mut v_a_3680_: *mut LeanObject,
    mut v_a_3681_: *mut LeanObject,
    mut v_a_3682_: *mut LeanObject,
    mut v_a_3683_: *mut LeanObject,
    mut v_a_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3697_: u8 = 0;
    let mut v_strict_3698_: u8 = 0;
    let mut v_strict_3699_: u8 = 0;
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3703_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_3698_ = lean_ctor_get_uint8(
                    v_k_x27_3673_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3698_ == 0 {
                    v_strict_3699_ = lean_ctor_get_uint8(
                        v_k_3671_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3699_ == 0 {
                        v___x_3700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
                        v___x_3701_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_3700_);
                        v___y_3687_ = v___x_3701_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3702_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4;
                        v___y_3687_ = v___x_3702_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_strict_3703_ = lean_ctor_get_uint8(
                        v_k_3671_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3703_ == 0 {
                        v___x_3704_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6;
                        v___y_3687_ = v___x_3704_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3705_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8;
                        v___y_3687_ = v___x_3705_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3688_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___y_3687_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
                if lean_obj_tag(v___x_3688_) == 0 {
                    v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
                    v_isSharedCheck_3697_ = (!lean_is_exclusive(v___x_3688_)) as u8;
                    if v_isSharedCheck_3697_ == 0 {
                        v___x_3691_ = v___x_3688_;
                        v_isShared_3692_ = v_isSharedCheck_3697_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3689_);
                        lean_dec(v___x_3688_);
                        v___x_3691_ = lean_box(0);
                        v_isShared_3692_ = v_isSharedCheck_3697_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_huv_3672_);
                    lean_dec_ref(v_v_3670_);
                    lean_dec_ref(v_u_3669_);
                    return v___x_3688_;
                }
            }
            2 => {
                v___x_3693_ = l_Lean_mkApp3(v_a_3689_, v_u_3669_, v_v_3670_, v_huv_3672_);
                if v_isShared_3692_ == 0 {
                    lean_ctor_set(v___x_3691_, 0, v___x_3693_);
                    v___x_3695_ = v___x_3691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
                    v___x_3695_ = v_reuseFailAlloc_3696_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3706_: *mut LeanObject = *_args.add(0);
    let mut v_v_3707_: *mut LeanObject = *_args.add(1);
    let mut v_k_3708_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3709_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3710_: *mut LeanObject = *_args.add(4);
    let mut v_a_3711_: *mut LeanObject = *_args.add(5);
    let mut v_a_3712_: *mut LeanObject = *_args.add(6);
    let mut v_a_3713_: *mut LeanObject = *_args.add(7);
    let mut v_a_3714_: *mut LeanObject = *_args.add(8);
    let mut v_a_3715_: *mut LeanObject = *_args.add(9);
    let mut v_a_3716_: *mut LeanObject = *_args.add(10);
    let mut v_a_3717_: *mut LeanObject = *_args.add(11);
    let mut v_a_3718_: *mut LeanObject = *_args.add(12);
    let mut v_a_3719_: *mut LeanObject = *_args.add(13);
    let mut v_a_3720_: *mut LeanObject = *_args.add(14);
    let mut v_a_3721_: *mut LeanObject = *_args.add(15);
    let mut v_a_3722_: *mut LeanObject = *_args.add(16);
    let mut v_res_3723_: *mut LeanObject = core::ptr::null_mut();
    v_res_3723_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_3706_, v_v_3707_, v_k_3708_, v_huv_3709_, v_k_x27_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
    lean_dec(v_a_3721_);
    lean_dec_ref(v_a_3720_);
    lean_dec(v_a_3719_);
    lean_dec_ref(v_a_3718_);
    lean_dec(v_a_3717_);
    lean_dec_ref(v_a_3716_);
    lean_dec(v_a_3715_);
    lean_dec_ref(v_a_3714_);
    lean_dec(v_a_3713_);
    lean_dec(v_a_3712_);
    lean_dec(v_a_3711_);
    lean_dec_ref(v_k_x27_3710_);
    lean_dec_ref(v_k_3708_);
    return v_res_3723_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(
    mut v_u_3748_: *mut LeanObject,
    mut v_v_3749_: *mut LeanObject,
    mut v_k_3750_: *mut LeanObject,
    mut v_huv_3751_: *mut LeanObject,
    mut v_k_x27_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3773_: u8 = 0;
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: u8 = 0;
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3804_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3807_: u8 = 0;
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3772_ = lean_ctor_get(v_k_x27_3752_, 0);
                v_strict_3773_ = lean_ctor_get_uint8(
                    v_k_x27_3752_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3773_ == 0 {
                    v_strict_3804_ = lean_ctor_get_uint8(
                        v_k_3750_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3804_ == 0 {
                        v___x_3805_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1;
                        v___y_3789_ = v___x_3805_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3806_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3;
                        v___y_3789_ = v___x_3806_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_strict_3807_ = lean_ctor_get_uint8(
                        v_k_3750_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_3807_ == 0 {
                        v___x_3808_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5;
                        v___y_3789_ = v___x_3808_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3809_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7;
                        v___y_3789_ = v___x_3809_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3769_ = l_Lean_eagerReflBoolTrue;
                v___x_3770_ = l_Lean_mkApp6(
                    v___y_3766_,
                    v_u_3748_,
                    v_v_3749_,
                    v___y_3767_,
                    v___y_3768_,
                    v___x_3769_,
                    v_huv_3751_,
                );
                v___x_3771_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3771_, 0, v___x_3770_);
                return v___x_3771_;
            }
            2 => {
                v___x_3777_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3778_ = lean_int_dec_le(v___x_3777_, v_k_3772_);
                if v___x_3778_ == 0 {
                    v___x_3779_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3780_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3781_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3782_ = lean_int_neg(v_k_3772_);
                    v___x_3783_ = l_Int_toNat(v___x_3782_);
                    lean_dec(v___x_3782_);
                    v___x_3784_ = l_Lean_instToExprInt_mkNat(v___x_3783_);
                    v___x_3785_ = l_Lean_mkApp3(v___x_3779_, v___x_3780_, v___x_3781_, v___x_3784_);
                    v___y_3766_ = v___y_3775_;
                    v___y_3767_ = v___y_3776_;
                    v___y_3768_ = v___x_3785_;
                    state = 1;
                    continue;
                } else {
                    v___x_3786_ = l_Int_toNat(v_k_3772_);
                    v___x_3787_ = l_Lean_instToExprInt_mkNat(v___x_3786_);
                    v___y_3766_ = v___y_3775_;
                    v___y_3767_ = v___y_3776_;
                    v___y_3768_ = v___x_3787_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_3789_);
                v___x_3790_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_3789_,
                    v_a_3753_,
                    v_a_3754_,
                    v_a_3755_,
                    v_a_3756_,
                    v_a_3757_,
                    v_a_3758_,
                    v_a_3759_,
                    v_a_3760_,
                    v_a_3761_,
                    v_a_3762_,
                    v_a_3763_,
                );
                if lean_obj_tag(v___x_3790_) == 0 {
                    v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
                    lean_inc(v_a_3791_);
                    lean_dec_ref_known(v___x_3790_, 1);
                    v_k_3792_ = lean_ctor_get(v_k_3750_, 0);
                    v___x_3793_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3794_ = lean_int_dec_le(v___x_3793_, v_k_3792_);
                    if v___x_3794_ == 0 {
                        v___x_3795_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3797_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3798_ = lean_int_neg(v_k_3792_);
                        v___x_3799_ = l_Int_toNat(v___x_3798_);
                        lean_dec(v___x_3798_);
                        v___x_3800_ = l_Lean_instToExprInt_mkNat(v___x_3799_);
                        v___x_3801_ =
                            l_Lean_mkApp3(v___x_3795_, v___x_3796_, v___x_3797_, v___x_3800_);
                        v___y_3775_ = v_a_3791_;
                        v___y_3776_ = v___x_3801_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3802_ = l_Int_toNat(v_k_3792_);
                        v___x_3803_ = l_Lean_instToExprInt_mkNat(v___x_3802_);
                        v___y_3775_ = v_a_3791_;
                        v___y_3776_ = v___x_3803_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_huv_3751_);
                    lean_dec_ref(v_v_3749_);
                    lean_dec_ref(v_u_3748_);
                    return v___x_3790_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3810_: *mut LeanObject = *_args.add(0);
    let mut v_v_3811_: *mut LeanObject = *_args.add(1);
    let mut v_k_3812_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3813_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3814_: *mut LeanObject = *_args.add(4);
    let mut v_a_3815_: *mut LeanObject = *_args.add(5);
    let mut v_a_3816_: *mut LeanObject = *_args.add(6);
    let mut v_a_3817_: *mut LeanObject = *_args.add(7);
    let mut v_a_3818_: *mut LeanObject = *_args.add(8);
    let mut v_a_3819_: *mut LeanObject = *_args.add(9);
    let mut v_a_3820_: *mut LeanObject = *_args.add(10);
    let mut v_a_3821_: *mut LeanObject = *_args.add(11);
    let mut v_a_3822_: *mut LeanObject = *_args.add(12);
    let mut v_a_3823_: *mut LeanObject = *_args.add(13);
    let mut v_a_3824_: *mut LeanObject = *_args.add(14);
    let mut v_a_3825_: *mut LeanObject = *_args.add(15);
    let mut v_a_3826_: *mut LeanObject = *_args.add(16);
    let mut v_res_3827_: *mut LeanObject = core::ptr::null_mut();
    v_res_3827_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_3810_, v_v_3811_, v_k_3812_, v_huv_3813_, v_k_x27_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
    lean_dec(v_a_3825_);
    lean_dec_ref(v_a_3824_);
    lean_dec(v_a_3823_);
    lean_dec_ref(v_a_3822_);
    lean_dec(v_a_3821_);
    lean_dec_ref(v_a_3820_);
    lean_dec(v_a_3819_);
    lean_dec_ref(v_a_3818_);
    lean_dec(v_a_3817_);
    lean_dec(v_a_3816_);
    lean_dec(v_a_3815_);
    lean_dec_ref(v_k_x27_3814_);
    lean_dec_ref(v_k_3812_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(
    mut v_u_3828_: *mut LeanObject,
    mut v_v_3829_: *mut LeanObject,
    mut v_k_3830_: *mut LeanObject,
    mut v_huv_3831_: *mut LeanObject,
    mut v_k_x27_3832_: *mut LeanObject,
    mut v_a_3833_: *mut LeanObject,
    mut v_a_3834_: *mut LeanObject,
    mut v_a_3835_: *mut LeanObject,
    mut v_a_3836_: *mut LeanObject,
    mut v_a_3837_: *mut LeanObject,
    mut v_a_3838_: *mut LeanObject,
    mut v_a_3839_: *mut LeanObject,
    mut v_a_3840_: *mut LeanObject,
    mut v_a_3841_: *mut LeanObject,
    mut v_a_3842_: *mut LeanObject,
    mut v_a_3843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3845_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_,
                    v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_,
                );
                if lean_obj_tag(v___x_3845_) == 0 {
                    v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
                    lean_inc(v_a_3846_);
                    lean_dec_ref_known(v___x_3845_, 1);
                    v___x_3847_ = (lean_unbox(v_a_3846_) as u8);
                    lean_dec(v_a_3846_);
                    if v___x_3847_ == 0 {
                        v___x_3848_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_3828_, v_v_3829_, v_k_3830_, v_huv_3831_, v_k_x27_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
                        return v___x_3848_;
                    } else {
                        v___x_3849_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_3828_, v_v_3829_, v_k_3830_, v_huv_3831_, v_k_x27_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
                        return v___x_3849_;
                    }
                } else {
                    lean_dec_ref(v_huv_3831_);
                    lean_dec_ref(v_v_3829_);
                    lean_dec_ref(v_u_3828_);
                    v_a_3850_ = lean_ctor_get(v___x_3845_, 0);
                    v_isSharedCheck_3857_ = (!lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3857_ == 0 {
                        v___x_3852_ = v___x_3845_;
                        v_isShared_3853_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3850_);
                        lean_dec(v___x_3845_);
                        v___x_3852_ = lean_box(0);
                        v_isShared_3853_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3853_ == 0 {
                    v___x_3855_ = v___x_3852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
                    v___x_3855_ = v_reuseFailAlloc_3856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3858_: *mut LeanObject = *_args.add(0);
    let mut v_v_3859_: *mut LeanObject = *_args.add(1);
    let mut v_k_3860_: *mut LeanObject = *_args.add(2);
    let mut v_huv_3861_: *mut LeanObject = *_args.add(3);
    let mut v_k_x27_3862_: *mut LeanObject = *_args.add(4);
    let mut v_a_3863_: *mut LeanObject = *_args.add(5);
    let mut v_a_3864_: *mut LeanObject = *_args.add(6);
    let mut v_a_3865_: *mut LeanObject = *_args.add(7);
    let mut v_a_3866_: *mut LeanObject = *_args.add(8);
    let mut v_a_3867_: *mut LeanObject = *_args.add(9);
    let mut v_a_3868_: *mut LeanObject = *_args.add(10);
    let mut v_a_3869_: *mut LeanObject = *_args.add(11);
    let mut v_a_3870_: *mut LeanObject = *_args.add(12);
    let mut v_a_3871_: *mut LeanObject = *_args.add(13);
    let mut v_a_3872_: *mut LeanObject = *_args.add(14);
    let mut v_a_3873_: *mut LeanObject = *_args.add(15);
    let mut v_a_3874_: *mut LeanObject = *_args.add(16);
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(
        v_u_3858_,
        v_v_3859_,
        v_k_3860_,
        v_huv_3861_,
        v_k_x27_3862_,
        v_a_3863_,
        v_a_3864_,
        v_a_3865_,
        v_a_3866_,
        v_a_3867_,
        v_a_3868_,
        v_a_3869_,
        v_a_3870_,
        v_a_3871_,
        v_a_3872_,
        v_a_3873_,
    );
    lean_dec(v_a_3873_);
    lean_dec_ref(v_a_3872_);
    lean_dec(v_a_3871_);
    lean_dec_ref(v_a_3870_);
    lean_dec(v_a_3869_);
    lean_dec_ref(v_a_3868_);
    lean_dec(v_a_3867_);
    lean_dec_ref(v_a_3866_);
    lean_dec(v_a_3865_);
    lean_dec(v_a_3864_);
    lean_dec(v_a_3863_);
    lean_dec_ref(v_k_x27_3862_);
    lean_dec_ref(v_k_3860_);
    return v_res_3875_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(
    mut v_u_3888_: *mut LeanObject,
    mut v_k_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
    mut v_a_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_3909_: u8 = 0;
    let mut v___y_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3908_ = lean_ctor_get(v_k_3889_, 0);
                v_strict_3909_ = lean_ctor_get_uint8(
                    v_k_3889_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_3909_ == 0 {
                    v___x_3925_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1;
                    v___y_3911_ = v___x_3925_;
                    state = 2;
                    continue;
                } else {
                    v___x_3926_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3;
                    v___y_3911_ = v___x_3926_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3905_ = l_Lean_eagerReflBoolTrue;
                v___x_3906_ = l_Lean_mkApp3(v___y_3903_, v_u_3888_, v___y_3904_, v___x_3905_);
                v___x_3907_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3907_, 0, v___x_3906_);
                return v___x_3907_;
            }
            2 => {
                lean_inc(v___y_3911_);
                v___x_3912_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_3911_,
                    v_a_3890_,
                    v_a_3891_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                    v_a_3896_,
                    v_a_3897_,
                    v_a_3898_,
                    v_a_3899_,
                    v_a_3900_,
                );
                if lean_obj_tag(v___x_3912_) == 0 {
                    v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
                    lean_inc(v_a_3913_);
                    lean_dec_ref_known(v___x_3912_, 1);
                    v___x_3914_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3915_ = lean_int_dec_le(v___x_3914_, v_k_3908_);
                    if v___x_3915_ == 0 {
                        v___x_3916_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3917_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3918_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3919_ = lean_int_neg(v_k_3908_);
                        v___x_3920_ = l_Int_toNat(v___x_3919_);
                        lean_dec(v___x_3919_);
                        v___x_3921_ = l_Lean_instToExprInt_mkNat(v___x_3920_);
                        v___x_3922_ =
                            l_Lean_mkApp3(v___x_3916_, v___x_3917_, v___x_3918_, v___x_3921_);
                        v___y_3903_ = v_a_3913_;
                        v___y_3904_ = v___x_3922_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3923_ = l_Int_toNat(v_k_3908_);
                        v___x_3924_ = l_Lean_instToExprInt_mkNat(v___x_3923_);
                        v___y_3903_ = v_a_3913_;
                        v___y_3904_ = v___x_3924_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_3888_);
                    return v___x_3912_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(
    mut v_u_3927_: *mut LeanObject,
    mut v_k_3928_: *mut LeanObject,
    mut v_a_3929_: *mut LeanObject,
    mut v_a_3930_: *mut LeanObject,
    mut v_a_3931_: *mut LeanObject,
    mut v_a_3932_: *mut LeanObject,
    mut v_a_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3941_: *mut LeanObject = core::ptr::null_mut();
    v_res_3941_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_3927_, v_k_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
    lean_dec(v_a_3939_);
    lean_dec_ref(v_a_3938_);
    lean_dec(v_a_3937_);
    lean_dec_ref(v_a_3936_);
    lean_dec(v_a_3935_);
    lean_dec_ref(v_a_3934_);
    lean_dec(v_a_3933_);
    lean_dec_ref(v_a_3932_);
    lean_dec(v_a_3931_);
    lean_dec(v_a_3930_);
    lean_dec(v_a_3929_);
    lean_dec_ref(v_k_3928_);
    return v_res_3941_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(
    mut v_u_3948_: *mut LeanObject,
    mut v_a_3949_: *mut LeanObject,
    mut v_a_3950_: *mut LeanObject,
    mut v_a_3951_: *mut LeanObject,
    mut v_a_3952_: *mut LeanObject,
    mut v_a_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
    mut v_a_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3961_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1;
                v___x_3962_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_3961_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
                if lean_obj_tag(v___x_3962_) == 0 {
                    v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
                    v_isSharedCheck_3971_ = (!lean_is_exclusive(v___x_3962_)) as u8;
                    if v_isSharedCheck_3971_ == 0 {
                        v___x_3965_ = v___x_3962_;
                        v_isShared_3966_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3963_);
                        lean_dec(v___x_3962_);
                        v___x_3965_ = lean_box(0);
                        v_isShared_3966_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_3948_);
                    return v___x_3962_;
                }
            }
            1 => {
                v___x_3967_ = l_Lean_Expr_app___override(v_a_3963_, v_u_3948_);
                if v_isShared_3966_ == 0 {
                    lean_ctor_set(v___x_3965_, 0, v___x_3967_);
                    v___x_3969_ = v___x_3965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
                    v___x_3969_ = v_reuseFailAlloc_3970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___boxed(
    mut v_u_3972_: *mut LeanObject,
    mut v_a_3973_: *mut LeanObject,
    mut v_a_3974_: *mut LeanObject,
    mut v_a_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
    mut v_a_3977_: *mut LeanObject,
    mut v_a_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
    mut v_a_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3985_: *mut LeanObject = core::ptr::null_mut();
    v_res_3985_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
    lean_dec(v_a_3983_);
    lean_dec_ref(v_a_3982_);
    lean_dec(v_a_3981_);
    lean_dec_ref(v_a_3980_);
    lean_dec(v_a_3979_);
    lean_dec_ref(v_a_3978_);
    lean_dec(v_a_3977_);
    lean_dec_ref(v_a_3976_);
    lean_dec(v_a_3975_);
    lean_dec(v_a_3974_);
    lean_dec(v_a_3973_);
    return v_res_3985_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2()
-> *mut LeanObject {
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1;
    v___x_3989_ = lean_unsigned_to_nat(4);
    v___x_3990_ = lean_unsigned_to_nat(228);
    v___x_3991_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0;
    v___x_3992_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0;
    v___x_3993_ = l_mkPanicMessageWithDecl(
        v___x_3992_,
        v___x_3991_,
        v___x_3990_,
        v___x_3989_,
        v___x_3988_,
    );
    return v___x_3993_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(
    mut v_u_3994_: *mut LeanObject,
    mut v_k_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v_strict_4011_: u8 = 0;
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4008_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_,
                    v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_,
                );
                if lean_obj_tag(v___x_4008_) == 0 {
                    v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
                    lean_inc(v_a_4009_);
                    lean_dec_ref_known(v___x_4008_, 1);
                    v___x_4010_ = (lean_unbox(v_a_4009_) as u8);
                    lean_dec(v_a_4009_);
                    if v___x_4010_ == 0 {
                        v_strict_4011_ = lean_ctor_get_uint8(
                            v_k_3995_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_strict_4011_ == 0 {
                            lean_dec_ref(v_u_3994_);
                            v___x_4012_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once), _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
                            v___x_4013_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_4012_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
                            return v___x_4013_;
                        } else {
                            v___x_4014_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
                            return v___x_4014_;
                        }
                    } else {
                        v___x_4015_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_3994_, v_k_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
                        return v___x_4015_;
                    }
                } else {
                    lean_dec_ref(v_u_3994_);
                    v_a_4016_ = lean_ctor_get(v___x_4008_, 0);
                    v_isSharedCheck_4023_ = (!lean_is_exclusive(v___x_4008_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4018_ = v___x_4008_;
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4016_);
                        lean_dec(v___x_4008_);
                        v___x_4018_ = lean_box(0);
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4019_ == 0 {
                    v___x_4021_ = v___x_4018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
                    v___x_4021_ = v_reuseFailAlloc_4022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___boxed(
    mut v_u_4024_: *mut LeanObject,
    mut v_k_4025_: *mut LeanObject,
    mut v_a_4026_: *mut LeanObject,
    mut v_a_4027_: *mut LeanObject,
    mut v_a_4028_: *mut LeanObject,
    mut v_a_4029_: *mut LeanObject,
    mut v_a_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_a_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
    mut v_a_4036_: *mut LeanObject,
    mut v_a_4037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4038_: *mut LeanObject = core::ptr::null_mut();
    v_res_4038_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(
        v_u_4024_, v_k_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_,
        v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_,
    );
    lean_dec(v_a_4036_);
    lean_dec_ref(v_a_4035_);
    lean_dec(v_a_4034_);
    lean_dec_ref(v_a_4033_);
    lean_dec(v_a_4032_);
    lean_dec_ref(v_a_4031_);
    lean_dec(v_a_4030_);
    lean_dec_ref(v_a_4029_);
    lean_dec(v_a_4028_);
    lean_dec(v_a_4027_);
    lean_dec(v_a_4026_);
    lean_dec_ref(v_k_4025_);
    return v_res_4038_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(
    mut v_u_4045_: *mut LeanObject,
    mut v_h_4046_: *mut LeanObject,
    mut v_a_4047_: *mut LeanObject,
    mut v_a_4048_: *mut LeanObject,
    mut v_a_4049_: *mut LeanObject,
    mut v_a_4050_: *mut LeanObject,
    mut v_a_4051_: *mut LeanObject,
    mut v_a_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
    mut v_a_4054_: *mut LeanObject,
    mut v_a_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4059_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1;
                v___x_4060_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_4059_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
                if lean_obj_tag(v___x_4060_) == 0 {
                    v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
                    v_isSharedCheck_4069_ = (!lean_is_exclusive(v___x_4060_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v___x_4063_ = v___x_4060_;
                        v_isShared_4064_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4061_);
                        lean_dec(v___x_4060_);
                        v___x_4063_ = lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_4046_);
                    lean_dec_ref(v_u_4045_);
                    return v___x_4060_;
                }
            }
            1 => {
                v___x_4065_ = l_Lean_mkAppB(v_a_4061_, v_u_4045_, v_h_4046_);
                if v_isShared_4064_ == 0 {
                    lean_ctor_set(v___x_4063_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4063_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___boxed(
    mut v_u_4070_: *mut LeanObject,
    mut v_h_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
    mut v_a_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
    mut v_a_4080_: *mut LeanObject,
    mut v_a_4081_: *mut LeanObject,
    mut v_a_4082_: *mut LeanObject,
    mut v_a_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4084_: *mut LeanObject = core::ptr::null_mut();
    v_res_4084_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_4070_, v_h_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
    lean_dec(v_a_4082_);
    lean_dec_ref(v_a_4081_);
    lean_dec(v_a_4080_);
    lean_dec_ref(v_a_4079_);
    lean_dec(v_a_4078_);
    lean_dec_ref(v_a_4077_);
    lean_dec(v_a_4076_);
    lean_dec_ref(v_a_4075_);
    lean_dec(v_a_4074_);
    lean_dec(v_a_4073_);
    lean_dec(v_a_4072_);
    return v_res_4084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(
    mut v_u_4097_: *mut LeanObject,
    mut v_k_4098_: *mut LeanObject,
    mut v_h_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
    mut v_a_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v_a_4106_: *mut LeanObject,
    mut v_a_4107_: *mut LeanObject,
    mut v_a_4108_: *mut LeanObject,
    mut v_a_4109_: *mut LeanObject,
    mut v_a_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4119_: u8 = 0;
    let mut v___y_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4118_ = lean_ctor_get(v_k_4098_, 0);
                v_strict_4119_ = lean_ctor_get_uint8(
                    v_k_4098_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_4119_ == 0 {
                    v___x_4135_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1;
                    v___y_4121_ = v___x_4135_;
                    state = 2;
                    continue;
                } else {
                    v___x_4136_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3;
                    v___y_4121_ = v___x_4136_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4115_ = l_Lean_eagerReflBoolTrue;
                v___x_4116_ =
                    l_Lean_mkApp4(v___y_4113_, v_u_4097_, v___y_4114_, v___x_4115_, v_h_4099_);
                v___x_4117_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4117_, 0, v___x_4116_);
                return v___x_4117_;
            }
            2 => {
                lean_inc(v___y_4121_);
                v___x_4122_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_4121_,
                    v_a_4100_,
                    v_a_4101_,
                    v_a_4102_,
                    v_a_4103_,
                    v_a_4104_,
                    v_a_4105_,
                    v_a_4106_,
                    v_a_4107_,
                    v_a_4108_,
                    v_a_4109_,
                    v_a_4110_,
                );
                if lean_obj_tag(v___x_4122_) == 0 {
                    v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
                    lean_inc(v_a_4123_);
                    lean_dec_ref_known(v___x_4122_, 1);
                    v___x_4124_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_4125_ = lean_int_dec_le(v___x_4124_, v_k_4118_);
                    if v___x_4125_ == 0 {
                        v___x_4126_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_4127_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_4128_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_4129_ = lean_int_neg(v_k_4118_);
                        v___x_4130_ = l_Int_toNat(v___x_4129_);
                        lean_dec(v___x_4129_);
                        v___x_4131_ = l_Lean_instToExprInt_mkNat(v___x_4130_);
                        v___x_4132_ =
                            l_Lean_mkApp3(v___x_4126_, v___x_4127_, v___x_4128_, v___x_4131_);
                        v___y_4113_ = v_a_4123_;
                        v___y_4114_ = v___x_4132_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4133_ = l_Int_toNat(v_k_4118_);
                        v___x_4134_ = l_Lean_instToExprInt_mkNat(v___x_4133_);
                        v___y_4113_ = v_a_4123_;
                        v___y_4114_ = v___x_4134_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_4099_);
                    lean_dec_ref(v_u_4097_);
                    return v___x_4122_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(
    mut v_u_4137_: *mut LeanObject,
    mut v_k_4138_: *mut LeanObject,
    mut v_h_4139_: *mut LeanObject,
    mut v_a_4140_: *mut LeanObject,
    mut v_a_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
    mut v_a_4143_: *mut LeanObject,
    mut v_a_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
    mut v_a_4146_: *mut LeanObject,
    mut v_a_4147_: *mut LeanObject,
    mut v_a_4148_: *mut LeanObject,
    mut v_a_4149_: *mut LeanObject,
    mut v_a_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4152_: *mut LeanObject = core::ptr::null_mut();
    v_res_4152_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_4137_, v_k_4138_, v_h_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
    lean_dec(v_a_4150_);
    lean_dec_ref(v_a_4149_);
    lean_dec(v_a_4148_);
    lean_dec_ref(v_a_4147_);
    lean_dec(v_a_4146_);
    lean_dec_ref(v_a_4145_);
    lean_dec(v_a_4144_);
    lean_dec_ref(v_a_4143_);
    lean_dec(v_a_4142_);
    lean_dec(v_a_4141_);
    lean_dec(v_a_4140_);
    lean_dec_ref(v_k_4138_);
    return v_res_4152_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkSelfUnsatProof(
    mut v_u_4153_: *mut LeanObject,
    mut v_k_4154_: *mut LeanObject,
    mut v_h_4155_: *mut LeanObject,
    mut v_a_4156_: *mut LeanObject,
    mut v_a_4157_: *mut LeanObject,
    mut v_a_4158_: *mut LeanObject,
    mut v_a_4159_: *mut LeanObject,
    mut v_a_4160_: *mut LeanObject,
    mut v_a_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
    mut v_a_4164_: *mut LeanObject,
    mut v_a_4165_: *mut LeanObject,
    mut v_a_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4168_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_,
                    v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_,
                );
                if lean_obj_tag(v___x_4168_) == 0 {
                    v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
                    lean_inc(v_a_4169_);
                    lean_dec_ref_known(v___x_4168_, 1);
                    v___x_4170_ = (lean_unbox(v_a_4169_) as u8);
                    lean_dec(v_a_4169_);
                    if v___x_4170_ == 0 {
                        v___x_4171_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_4153_, v_h_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                        return v___x_4171_;
                    } else {
                        v___x_4172_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_4153_, v_k_4154_, v_h_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                        return v___x_4172_;
                    }
                } else {
                    lean_dec_ref(v_h_4155_);
                    lean_dec_ref(v_u_4153_);
                    v_a_4173_ = lean_ctor_get(v___x_4168_, 0);
                    v_isSharedCheck_4180_ = (!lean_is_exclusive(v___x_4168_)) as u8;
                    if v_isSharedCheck_4180_ == 0 {
                        v___x_4175_ = v___x_4168_;
                        v_isShared_4176_ = v_isSharedCheck_4180_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4173_);
                        lean_dec(v___x_4168_);
                        v___x_4175_ = lean_box(0);
                        v_isShared_4176_ = v_isSharedCheck_4180_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkSelfUnsatProof___boxed(
    mut v_u_4181_: *mut LeanObject,
    mut v_k_4182_: *mut LeanObject,
    mut v_h_4183_: *mut LeanObject,
    mut v_a_4184_: *mut LeanObject,
    mut v_a_4185_: *mut LeanObject,
    mut v_a_4186_: *mut LeanObject,
    mut v_a_4187_: *mut LeanObject,
    mut v_a_4188_: *mut LeanObject,
    mut v_a_4189_: *mut LeanObject,
    mut v_a_4190_: *mut LeanObject,
    mut v_a_4191_: *mut LeanObject,
    mut v_a_4192_: *mut LeanObject,
    mut v_a_4193_: *mut LeanObject,
    mut v_a_4194_: *mut LeanObject,
    mut v_a_4195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4196_: *mut LeanObject = core::ptr::null_mut();
    v_res_4196_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(
        v_u_4181_, v_k_4182_, v_h_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_,
        v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_,
    );
    lean_dec(v_a_4194_);
    lean_dec_ref(v_a_4193_);
    lean_dec(v_a_4192_);
    lean_dec_ref(v_a_4191_);
    lean_dec(v_a_4190_);
    lean_dec_ref(v_a_4189_);
    lean_dec(v_a_4188_);
    lean_dec_ref(v_a_4187_);
    lean_dec(v_a_4186_);
    lean_dec(v_a_4185_);
    lean_dec(v_a_4184_);
    lean_dec_ref(v_k_4182_);
    return v_res_4196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2()
-> *mut LeanObject {
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    v___x_4199_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1;
    v___x_4200_ = lean_unsigned_to_nat(2);
    v___x_4201_ = lean_unsigned_to_nat(255);
    v___x_4202_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0;
    v___x_4203_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0;
    v___x_4204_ = l_mkPanicMessageWithDecl(
        v___x_4203_,
        v___x_4202_,
        v___x_4201_,
        v___x_4200_,
        v___x_4199_,
    );
    return v___x_4204_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(
    mut v_u_4205_: *mut LeanObject,
    mut v_v_4206_: *mut LeanObject,
    mut v_k_u2081_4207_: *mut LeanObject,
    mut v_h_u2081_4208_: *mut LeanObject,
    mut v_k_u2082_4209_: *mut LeanObject,
    mut v_h_u2082_4210_: *mut LeanObject,
    mut v_a_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
    mut v_a_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_strict_4223_: u8 = 0;
    let mut v_strict_4224_: u8 = 0;
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_4223_ = lean_ctor_get_uint8(
                    v_k_u2081_4207_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_strict_4224_ = lean_ctor_get_uint8(
                    v_k_u2082_4209_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_inc_ref_n(v_u_4205_, 2);
                v___x_4225_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_4205_, v_v_4206_, v_u_4205_, v_strict_4223_, v_strict_4224_, v_h_u2081_4208_, v_h_u2082_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
                if lean_obj_tag(v___x_4225_) == 0 {
                    v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
                    lean_inc(v_a_4226_);
                    lean_dec_ref_known(v___x_4225_, 1);
                    if v_strict_4223_ == 0 {
                        if v_strict_4224_ == 0 {
                            lean_dec(v_a_4226_);
                            lean_dec_ref(v_u_4205_);
                            v___x_4239_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
                            v___x_4240_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_4239_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
                            return v___x_4240_;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_4205_);
                    return v___x_4225_;
                }
            }
            1 => {
                v___x_4228_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1;
                v___x_4229_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_4228_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
                if lean_obj_tag(v___x_4229_) == 0 {
                    v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
                    v_isSharedCheck_4238_ = (!lean_is_exclusive(v___x_4229_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4232_ = v___x_4229_;
                        v_isShared_4233_ = v_isSharedCheck_4238_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4230_);
                        lean_dec(v___x_4229_);
                        v___x_4232_ = lean_box(0);
                        v_isShared_4233_ = v_isSharedCheck_4238_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4226_);
                    lean_dec_ref(v_u_4205_);
                    return v___x_4229_;
                }
            }
            2 => {
                v___x_4234_ = l_Lean_mkAppB(v_a_4230_, v_u_4205_, v_a_4226_);
                if v_isShared_4233_ == 0 {
                    lean_ctor_set(v___x_4232_, 0, v___x_4234_);
                    v___x_4236_ = v___x_4232_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
                    v___x_4236_ = v_reuseFailAlloc_4237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_4241_: *mut LeanObject = *_args.add(0);
    let mut v_v_4242_: *mut LeanObject = *_args.add(1);
    let mut v_k_u2081_4243_: *mut LeanObject = *_args.add(2);
    let mut v_h_u2081_4244_: *mut LeanObject = *_args.add(3);
    let mut v_k_u2082_4245_: *mut LeanObject = *_args.add(4);
    let mut v_h_u2082_4246_: *mut LeanObject = *_args.add(5);
    let mut v_a_4247_: *mut LeanObject = *_args.add(6);
    let mut v_a_4248_: *mut LeanObject = *_args.add(7);
    let mut v_a_4249_: *mut LeanObject = *_args.add(8);
    let mut v_a_4250_: *mut LeanObject = *_args.add(9);
    let mut v_a_4251_: *mut LeanObject = *_args.add(10);
    let mut v_a_4252_: *mut LeanObject = *_args.add(11);
    let mut v_a_4253_: *mut LeanObject = *_args.add(12);
    let mut v_a_4254_: *mut LeanObject = *_args.add(13);
    let mut v_a_4255_: *mut LeanObject = *_args.add(14);
    let mut v_a_4256_: *mut LeanObject = *_args.add(15);
    let mut v_a_4257_: *mut LeanObject = *_args.add(16);
    let mut v_a_4258_: *mut LeanObject = *_args.add(17);
    let mut v_res_4259_: *mut LeanObject = core::ptr::null_mut();
    v_res_4259_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(
            v_u_4241_,
            v_v_4242_,
            v_k_u2081_4243_,
            v_h_u2081_4244_,
            v_k_u2082_4245_,
            v_h_u2082_4246_,
            v_a_4247_,
            v_a_4248_,
            v_a_4249_,
            v_a_4250_,
            v_a_4251_,
            v_a_4252_,
            v_a_4253_,
            v_a_4254_,
            v_a_4255_,
            v_a_4256_,
            v_a_4257_,
        );
    lean_dec(v_a_4257_);
    lean_dec_ref(v_a_4256_);
    lean_dec(v_a_4255_);
    lean_dec_ref(v_a_4254_);
    lean_dec(v_a_4253_);
    lean_dec_ref(v_a_4252_);
    lean_dec(v_a_4251_);
    lean_dec_ref(v_a_4250_);
    lean_dec(v_a_4249_);
    lean_dec(v_a_4248_);
    lean_dec(v_a_4247_);
    lean_dec_ref(v_k_u2082_4245_);
    lean_dec_ref(v_k_u2081_4243_);
    return v_res_4259_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(
    mut v_u_4260_: *mut LeanObject,
    mut v_v_4261_: *mut LeanObject,
    mut v_k_u2081_4262_: *mut LeanObject,
    mut v_h_u2081_4263_: *mut LeanObject,
    mut v_k_u2082_4264_: *mut LeanObject,
    mut v_h_u2082_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
    mut v_a_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
    mut v_a_4274_: *mut LeanObject,
    mut v_a_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___y_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4292_: u8 = 0;
    let mut v___y_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_strict_4312_: u8 = 0;
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref_n(v_u_4260_, 2);
                v___x_4278_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_4260_, v_v_4261_, v_u_4260_, v_k_u2081_4262_, v_k_u2082_4264_, v_h_u2081_4263_, v_h_u2082_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
                if lean_obj_tag(v___x_4278_) == 0 {
                    v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
                    v_isSharedCheck_4314_ = (!lean_is_exclusive(v___x_4278_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v___x_4281_ = v___x_4278_;
                        v_isShared_4282_ = v_isSharedCheck_4314_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4279_);
                        lean_dec(v___x_4278_);
                        v___x_4281_ = lean_box(0);
                        v_isShared_4282_ = v_isSharedCheck_4314_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_u_4260_);
                    return v___x_4278_;
                }
            }
            1 => {
                v_k_4291_ = lean_ctor_get(v_k_u2081_4262_, 0);
                v_strict_4292_ = lean_ctor_get_uint8(
                    v_k_u2081_4262_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_strict_4292_ == 0 {
                    v_strict_4312_ = lean_ctor_get_uint8(
                        v_k_u2082_4264_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_strict_4312_ == 0 {
                        v___x_4313_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1;
                        v___y_4294_ = v___x_4313_;
                        state = 4;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_4286_ = l_Lean_eagerReflBoolTrue;
                v___x_4287_ =
                    l_Lean_mkApp4(v___y_4284_, v_u_4260_, v___y_4285_, v___x_4286_, v_a_4279_);
                if v_isShared_4282_ == 0 {
                    lean_ctor_set(v___x_4281_, 0, v___x_4287_);
                    v___x_4289_ = v___x_4281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4289_;
            }
            4 => {
                lean_inc(v___y_4294_);
                v___x_4295_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
                    v___y_4294_,
                    v_a_4266_,
                    v_a_4267_,
                    v_a_4268_,
                    v_a_4269_,
                    v_a_4270_,
                    v_a_4271_,
                    v_a_4272_,
                    v_a_4273_,
                    v_a_4274_,
                    v_a_4275_,
                    v_a_4276_,
                );
                if lean_obj_tag(v___x_4295_) == 0 {
                    v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
                    lean_inc(v_a_4296_);
                    lean_dec_ref_known(v___x_4295_, 1);
                    v_k_4297_ = lean_ctor_get(v_k_u2082_4264_, 0);
                    v___x_4298_ = lean_int_add(v_k_4291_, v_k_4297_);
                    v___x_4299_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_4300_ = lean_int_dec_le(v___x_4299_, v___x_4298_);
                    if v___x_4300_ == 0 {
                        v___x_4301_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_4302_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_4303_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_4304_ = lean_int_neg(v___x_4298_);
                        lean_dec(v___x_4298_);
                        v___x_4305_ = l_Int_toNat(v___x_4304_);
                        lean_dec(v___x_4304_);
                        v___x_4306_ = l_Lean_instToExprInt_mkNat(v___x_4305_);
                        v___x_4307_ =
                            l_Lean_mkApp3(v___x_4301_, v___x_4302_, v___x_4303_, v___x_4306_);
                        v___y_4284_ = v_a_4296_;
                        v___y_4285_ = v___x_4307_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4308_ = l_Int_toNat(v___x_4298_);
                        lean_dec(v___x_4298_);
                        v___x_4309_ = l_Lean_instToExprInt_mkNat(v___x_4308_);
                        v___y_4284_ = v_a_4296_;
                        v___y_4285_ = v___x_4309_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4281_);
                    lean_dec(v_a_4279_);
                    lean_dec_ref(v_u_4260_);
                    return v___x_4295_;
                }
            }
            5 => {
                v___x_4311_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3;
                v___y_4294_ = v___x_4311_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_4315_: *mut LeanObject = *_args.add(0);
    let mut v_v_4316_: *mut LeanObject = *_args.add(1);
    let mut v_k_u2081_4317_: *mut LeanObject = *_args.add(2);
    let mut v_h_u2081_4318_: *mut LeanObject = *_args.add(3);
    let mut v_k_u2082_4319_: *mut LeanObject = *_args.add(4);
    let mut v_h_u2082_4320_: *mut LeanObject = *_args.add(5);
    let mut v_a_4321_: *mut LeanObject = *_args.add(6);
    let mut v_a_4322_: *mut LeanObject = *_args.add(7);
    let mut v_a_4323_: *mut LeanObject = *_args.add(8);
    let mut v_a_4324_: *mut LeanObject = *_args.add(9);
    let mut v_a_4325_: *mut LeanObject = *_args.add(10);
    let mut v_a_4326_: *mut LeanObject = *_args.add(11);
    let mut v_a_4327_: *mut LeanObject = *_args.add(12);
    let mut v_a_4328_: *mut LeanObject = *_args.add(13);
    let mut v_a_4329_: *mut LeanObject = *_args.add(14);
    let mut v_a_4330_: *mut LeanObject = *_args.add(15);
    let mut v_a_4331_: *mut LeanObject = *_args.add(16);
    let mut v_a_4332_: *mut LeanObject = *_args.add(17);
    let mut v_res_4333_: *mut LeanObject = core::ptr::null_mut();
    v_res_4333_ =
        l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(
            v_u_4315_,
            v_v_4316_,
            v_k_u2081_4317_,
            v_h_u2081_4318_,
            v_k_u2082_4319_,
            v_h_u2082_4320_,
            v_a_4321_,
            v_a_4322_,
            v_a_4323_,
            v_a_4324_,
            v_a_4325_,
            v_a_4326_,
            v_a_4327_,
            v_a_4328_,
            v_a_4329_,
            v_a_4330_,
            v_a_4331_,
        );
    lean_dec(v_a_4331_);
    lean_dec_ref(v_a_4330_);
    lean_dec(v_a_4329_);
    lean_dec_ref(v_a_4328_);
    lean_dec(v_a_4327_);
    lean_dec_ref(v_a_4326_);
    lean_dec(v_a_4325_);
    lean_dec_ref(v_a_4324_);
    lean_dec(v_a_4323_);
    lean_dec(v_a_4322_);
    lean_dec(v_a_4321_);
    lean_dec_ref(v_k_u2082_4319_);
    lean_dec_ref(v_k_u2081_4317_);
    return v_res_4333_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkUnsatProof(
    mut v_u_4334_: *mut LeanObject,
    mut v_v_4335_: *mut LeanObject,
    mut v_k_u2081_4336_: *mut LeanObject,
    mut v_h_u2081_4337_: *mut LeanObject,
    mut v_k_u2082_4338_: *mut LeanObject,
    mut v_h_u2082_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
    mut v_a_4343_: *mut LeanObject,
    mut v_a_4344_: *mut LeanObject,
    mut v_a_4345_: *mut LeanObject,
    mut v_a_4346_: *mut LeanObject,
    mut v_a_4347_: *mut LeanObject,
    mut v_a_4348_: *mut LeanObject,
    mut v_a_4349_: *mut LeanObject,
    mut v_a_4350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4352_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_,
                    v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_,
                );
                if lean_obj_tag(v___x_4352_) == 0 {
                    v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
                    lean_inc(v_a_4353_);
                    lean_dec_ref_known(v___x_4352_, 1);
                    v___x_4354_ = (lean_unbox(v_a_4353_) as u8);
                    lean_dec(v_a_4353_);
                    if v___x_4354_ == 0 {
                        v___x_4355_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_4334_, v_v_4335_, v_k_u2081_4336_, v_h_u2081_4337_, v_k_u2082_4338_, v_h_u2082_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
                        return v___x_4355_;
                    } else {
                        v___x_4356_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_4334_, v_v_4335_, v_k_u2081_4336_, v_h_u2081_4337_, v_k_u2082_4338_, v_h_u2082_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
                        return v___x_4356_;
                    }
                } else {
                    lean_dec_ref(v_h_u2082_4339_);
                    lean_dec_ref(v_h_u2081_4337_);
                    lean_dec_ref(v_v_4335_);
                    lean_dec_ref(v_u_4334_);
                    v_a_4357_ = lean_ctor_get(v___x_4352_, 0);
                    v_isSharedCheck_4364_ = (!lean_is_exclusive(v___x_4352_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4359_ = v___x_4352_;
                        v_isShared_4360_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4357_);
                        lean_dec(v___x_4352_);
                        v___x_4359_ = lean_box(0);
                        v_isShared_4360_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4360_ == 0 {
                    v___x_4362_ = v___x_4359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
                    v___x_4362_ = v_reuseFailAlloc_4363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkUnsatProof___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_4365_: *mut LeanObject = *_args.add(0);
    let mut v_v_4366_: *mut LeanObject = *_args.add(1);
    let mut v_k_u2081_4367_: *mut LeanObject = *_args.add(2);
    let mut v_h_u2081_4368_: *mut LeanObject = *_args.add(3);
    let mut v_k_u2082_4369_: *mut LeanObject = *_args.add(4);
    let mut v_h_u2082_4370_: *mut LeanObject = *_args.add(5);
    let mut v_a_4371_: *mut LeanObject = *_args.add(6);
    let mut v_a_4372_: *mut LeanObject = *_args.add(7);
    let mut v_a_4373_: *mut LeanObject = *_args.add(8);
    let mut v_a_4374_: *mut LeanObject = *_args.add(9);
    let mut v_a_4375_: *mut LeanObject = *_args.add(10);
    let mut v_a_4376_: *mut LeanObject = *_args.add(11);
    let mut v_a_4377_: *mut LeanObject = *_args.add(12);
    let mut v_a_4378_: *mut LeanObject = *_args.add(13);
    let mut v_a_4379_: *mut LeanObject = *_args.add(14);
    let mut v_a_4380_: *mut LeanObject = *_args.add(15);
    let mut v_a_4381_: *mut LeanObject = *_args.add(16);
    let mut v_a_4382_: *mut LeanObject = *_args.add(17);
    let mut v_res_4383_: *mut LeanObject = core::ptr::null_mut();
    v_res_4383_ = l_Lean_Meta_Grind_Order_mkUnsatProof(
        v_u_4365_,
        v_v_4366_,
        v_k_u2081_4367_,
        v_h_u2081_4368_,
        v_k_u2082_4369_,
        v_h_u2082_4370_,
        v_a_4371_,
        v_a_4372_,
        v_a_4373_,
        v_a_4374_,
        v_a_4375_,
        v_a_4376_,
        v_a_4377_,
        v_a_4378_,
        v_a_4379_,
        v_a_4380_,
        v_a_4381_,
    );
    lean_dec(v_a_4381_);
    lean_dec_ref(v_a_4380_);
    lean_dec(v_a_4379_);
    lean_dec_ref(v_a_4378_);
    lean_dec(v_a_4377_);
    lean_dec_ref(v_a_4376_);
    lean_dec(v_a_4375_);
    lean_dec_ref(v_a_4374_);
    lean_dec(v_a_4373_);
    lean_dec(v_a_4372_);
    lean_dec(v_a_4371_);
    lean_dec_ref(v_k_u2082_4369_);
    lean_dec_ref(v_k_u2081_4367_);
    return v_res_4383_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(
    mut v_u_4390_: *mut LeanObject,
    mut v_v_4391_: *mut LeanObject,
    mut v_h_u2081_4392_: *mut LeanObject,
    mut v_h_u2082_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
    mut v_a_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
    mut v_a_4401_: *mut LeanObject,
    mut v_a_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
    mut v_a_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4406_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1;
                v___x_4407_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_4406_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
                if lean_obj_tag(v___x_4407_) == 0 {
                    v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
                    v_isSharedCheck_4416_ = (!lean_is_exclusive(v___x_4407_)) as u8;
                    if v_isSharedCheck_4416_ == 0 {
                        v___x_4410_ = v___x_4407_;
                        v_isShared_4411_ = v_isSharedCheck_4416_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4408_);
                        lean_dec(v___x_4407_);
                        v___x_4410_ = lean_box(0);
                        v_isShared_4411_ = v_isSharedCheck_4416_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u2082_4393_);
                    lean_dec_ref(v_h_u2081_4392_);
                    lean_dec_ref(v_v_4391_);
                    lean_dec_ref(v_u_4390_);
                    return v___x_4407_;
                }
            }
            1 => {
                v___x_4412_ = l_Lean_mkApp4(
                    v_a_4408_,
                    v_u_4390_,
                    v_v_4391_,
                    v_h_u2081_4392_,
                    v_h_u2082_4393_,
                );
                if v_isShared_4411_ == 0 {
                    lean_ctor_set(v___x_4410_, 0, v___x_4412_);
                    v___x_4414_ = v___x_4410_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
                    v___x_4414_ = v_reuseFailAlloc_4415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___boxed(
    mut v_u_4417_: *mut LeanObject,
    mut v_v_4418_: *mut LeanObject,
    mut v_h_u2081_4419_: *mut LeanObject,
    mut v_h_u2082_4420_: *mut LeanObject,
    mut v_a_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
    mut v_a_4429_: *mut LeanObject,
    mut v_a_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_a_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4433_: *mut LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(
        v_u_4417_,
        v_v_4418_,
        v_h_u2081_4419_,
        v_h_u2082_4420_,
        v_a_4421_,
        v_a_4422_,
        v_a_4423_,
        v_a_4424_,
        v_a_4425_,
        v_a_4426_,
        v_a_4427_,
        v_a_4428_,
        v_a_4429_,
        v_a_4430_,
        v_a_4431_,
    );
    lean_dec(v_a_4431_);
    lean_dec_ref(v_a_4430_);
    lean_dec(v_a_4429_);
    lean_dec_ref(v_a_4428_);
    lean_dec(v_a_4427_);
    lean_dec_ref(v_a_4426_);
    lean_dec(v_a_4425_);
    lean_dec_ref(v_a_4424_);
    lean_dec(v_a_4423_);
    lean_dec(v_a_4422_);
    lean_dec(v_a_4421_);
    return v_res_4433_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(
    mut v_u_4440_: *mut LeanObject,
    mut v_v_4441_: *mut LeanObject,
    mut v_h_u2081_4442_: *mut LeanObject,
    mut v_h_u2082_4443_: *mut LeanObject,
    mut v_a_4444_: *mut LeanObject,
    mut v_a_4445_: *mut LeanObject,
    mut v_a_4446_: *mut LeanObject,
    mut v_a_4447_: *mut LeanObject,
    mut v_a_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___y_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4456_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1;
                v___x_4457_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_4456_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
                if lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
                    lean_inc(v_a_4458_);
                    lean_dec_ref_known(v___x_4457_, 1);
                    v___x_4459_ = l_Lean_Meta_Grind_Order_getStruct(
                        v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_,
                        v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_,
                    );
                    if lean_obj_tag(v___x_4459_) == 0 {
                        v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v___x_4462_ = v___x_4459_;
                            v_isShared_4463_ = v_isSharedCheck_4475_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4460_);
                            lean_dec(v___x_4459_);
                            v___x_4462_ = lean_box(0);
                            v_isShared_4463_ = v_isSharedCheck_4475_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4458_);
                        lean_dec_ref(v_h_u2082_4443_);
                        lean_dec_ref(v_h_u2081_4442_);
                        lean_dec_ref(v_v_4441_);
                        lean_dec_ref(v_u_4440_);
                        v_a_4476_ = lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4483_ = (!lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4478_ = v___x_4459_;
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4476_);
                            lean_dec(v___x_4459_);
                            v___x_4478_ = lean_box(0);
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_u2082_4443_);
                    lean_dec_ref(v_h_u2081_4442_);
                    lean_dec_ref(v_v_4441_);
                    lean_dec_ref(v_u_4440_);
                    return v___x_4457_;
                }
            }
            1 => {
                v_ringInst_x3f_4471_ = lean_ctor_get(v_a_4460_, 10);
                lean_inc(v_ringInst_x3f_4471_);
                lean_dec(v_a_4460_);
                if lean_obj_tag(v_ringInst_x3f_4471_) == 0 {
                    v___x_4472_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_4473_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_4472_);
                    v___y_4465_ = v___x_4473_;
                    state = 2;
                    continue;
                } else {
                    v_val_4474_ = lean_ctor_get(v_ringInst_x3f_4471_, 0);
                    lean_inc(v_val_4474_);
                    lean_dec_ref_known(v_ringInst_x3f_4471_, 1);
                    v___y_4465_ = v_val_4474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4466_ = l_Lean_Expr_app___override(v_a_4458_, v___y_4465_);
                v___x_4467_ = l_Lean_mkApp4(
                    v___x_4466_,
                    v_u_4440_,
                    v_v_4441_,
                    v_h_u2081_4442_,
                    v_h_u2082_4443_,
                );
                if v_isShared_4463_ == 0 {
                    lean_ctor_set(v___x_4462_, 0, v___x_4467_);
                    v___x_4469_ = v___x_4462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
                    v___x_4469_ = v_reuseFailAlloc_4470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4469_;
            }
            4 => {
                if v_isShared_4479_ == 0 {
                    v___x_4481_ = v___x_4478_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___boxed(
    mut v_u_4484_: *mut LeanObject,
    mut v_v_4485_: *mut LeanObject,
    mut v_h_u2081_4486_: *mut LeanObject,
    mut v_h_u2082_4487_: *mut LeanObject,
    mut v_a_4488_: *mut LeanObject,
    mut v_a_4489_: *mut LeanObject,
    mut v_a_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
    mut v_a_4492_: *mut LeanObject,
    mut v_a_4493_: *mut LeanObject,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
    mut v_a_4497_: *mut LeanObject,
    mut v_a_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4500_: *mut LeanObject = core::ptr::null_mut();
    v_res_4500_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(
        v_u_4484_,
        v_v_4485_,
        v_h_u2081_4486_,
        v_h_u2082_4487_,
        v_a_4488_,
        v_a_4489_,
        v_a_4490_,
        v_a_4491_,
        v_a_4492_,
        v_a_4493_,
        v_a_4494_,
        v_a_4495_,
        v_a_4496_,
        v_a_4497_,
        v_a_4498_,
    );
    lean_dec(v_a_4498_);
    lean_dec_ref(v_a_4497_);
    lean_dec(v_a_4496_);
    lean_dec_ref(v_a_4495_);
    lean_dec(v_a_4494_);
    lean_dec_ref(v_a_4493_);
    lean_dec(v_a_4492_);
    lean_dec_ref(v_a_4491_);
    lean_dec(v_a_4490_);
    lean_dec(v_a_4489_);
    lean_dec(v_a_4488_);
    return v_res_4500_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(
    mut v_u_4501_: *mut LeanObject,
    mut v_v_4502_: *mut LeanObject,
    mut v_h_u2081_4503_: *mut LeanObject,
    mut v_h_u2082_4504_: *mut LeanObject,
    mut v_a_4505_: *mut LeanObject,
    mut v_a_4506_: *mut LeanObject,
    mut v_a_4507_: *mut LeanObject,
    mut v_a_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
    mut v_a_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4517_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_,
                    v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_,
                );
                if lean_obj_tag(v___x_4517_) == 0 {
                    v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
                    lean_inc(v_a_4518_);
                    lean_dec_ref_known(v___x_4517_, 1);
                    v___x_4519_ = (lean_unbox(v_a_4518_) as u8);
                    lean_dec(v_a_4518_);
                    if v___x_4519_ == 0 {
                        v___x_4520_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(
                            v_u_4501_,
                            v_v_4502_,
                            v_h_u2081_4503_,
                            v_h_u2082_4504_,
                            v_a_4505_,
                            v_a_4506_,
                            v_a_4507_,
                            v_a_4508_,
                            v_a_4509_,
                            v_a_4510_,
                            v_a_4511_,
                            v_a_4512_,
                            v_a_4513_,
                            v_a_4514_,
                            v_a_4515_,
                        );
                        return v___x_4520_;
                    } else {
                        v___x_4521_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(
                            v_u_4501_,
                            v_v_4502_,
                            v_h_u2081_4503_,
                            v_h_u2082_4504_,
                            v_a_4505_,
                            v_a_4506_,
                            v_a_4507_,
                            v_a_4508_,
                            v_a_4509_,
                            v_a_4510_,
                            v_a_4511_,
                            v_a_4512_,
                            v_a_4513_,
                            v_a_4514_,
                            v_a_4515_,
                        );
                        return v___x_4521_;
                    }
                } else {
                    lean_dec_ref(v_h_u2082_4504_);
                    lean_dec_ref(v_h_u2081_4503_);
                    lean_dec_ref(v_v_4502_);
                    lean_dec_ref(v_u_4501_);
                    v_a_4522_ = lean_ctor_get(v___x_4517_, 0);
                    v_isSharedCheck_4529_ = (!lean_is_exclusive(v___x_4517_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4524_ = v___x_4517_;
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4522_);
                        lean_dec(v___x_4517_);
                        v___x_4524_ = lean_box(0);
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4525_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe___boxed(
    mut v_u_4530_: *mut LeanObject,
    mut v_v_4531_: *mut LeanObject,
    mut v_h_u2081_4532_: *mut LeanObject,
    mut v_h_u2082_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
    mut v_a_4535_: *mut LeanObject,
    mut v_a_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
    mut v_a_4539_: *mut LeanObject,
    mut v_a_4540_: *mut LeanObject,
    mut v_a_4541_: *mut LeanObject,
    mut v_a_4542_: *mut LeanObject,
    mut v_a_4543_: *mut LeanObject,
    mut v_a_4544_: *mut LeanObject,
    mut v_a_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4546_: *mut LeanObject = core::ptr::null_mut();
    v_res_4546_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(
        v_u_4530_,
        v_v_4531_,
        v_h_u2081_4532_,
        v_h_u2082_4533_,
        v_a_4534_,
        v_a_4535_,
        v_a_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
        v_a_4541_,
        v_a_4542_,
        v_a_4543_,
        v_a_4544_,
    );
    lean_dec(v_a_4544_);
    lean_dec_ref(v_a_4543_);
    lean_dec(v_a_4542_);
    lean_dec_ref(v_a_4541_);
    lean_dec(v_a_4540_);
    lean_dec_ref(v_a_4539_);
    lean_dec(v_a_4538_);
    lean_dec_ref(v_a_4537_);
    lean_dec(v_a_4536_);
    lean_dec(v_a_4535_);
    lean_dec(v_a_4534_);
    return v_res_4546_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
}
