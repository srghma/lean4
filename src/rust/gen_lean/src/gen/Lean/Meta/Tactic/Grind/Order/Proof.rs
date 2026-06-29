// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Proof
// Imports: Lean.Meta.Tactic.Grind.Order.OrderM Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Init.Grind.Order
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Grind::Order::{
    initialize_Init_Grind_Order, runtime_initialize_Init_Grind_Order,
};
use crate::r#gen::Init::Prelude::l_instInhabitedForall___redArg___lam__0___boxed;
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
use crate::ffi::{
    lean_int_add, lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::ffi::{lean_nat_dec_lt, lean_panic_fn_borrowed};
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__3_value) as *mut crate::leanh::LeanObject,12648290874539584503 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 95, 108, 116, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__5_value) as *mut crate::leanh::LeanObject,7826207489827013974 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 116, 95, 108, 101, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__7_value) as *mut crate::leanh::LeanObject,16697182562648691278 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 116, 95, 116, 114, 97, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__9_value) as *mut crate::leanh::LeanObject,13335477371899428046 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__0_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__1_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__6_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__9_value) as *mut crate::leanh::LeanObject,6362876895233142233 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__12_value) as *mut crate::leanh::LeanObject,15439129730316893054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 101, 95, 108, 116, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__14_value) as *mut crate::leanh::LeanObject,2034847181816423711 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 116, 95, 108, 101, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__16_value) as *mut crate::leanh::LeanObject,3517412897252186849 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 116, 95, 116, 114, 97, 110, 115, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__18_value) as *mut crate::leanh::LeanObject,8748413887631389279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value: crate::leanh::LeanStringObject<95> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 95, m_capacity: 95, m_length: 94, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 69, 113, 84, 114, 117, 101, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 107, 46, 115, 116, 114, 105, 99, 116, 32, 38, 38, 32, 33, 107, 39, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__4_value) as *mut crate::leanh::LeanObject,17868538397656873279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__0_value) as *mut crate::leanh::LeanObject,3762829983402653789 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__2_value) as *mut crate::leanh::LeanObject,11946608431158487874 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__4_value) as *mut crate::leanh::LeanObject,2174632405960423778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__6_value) as *mut crate::leanh::LeanObject,2356419264488831487 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__0_value) as *mut crate::leanh::LeanObject,15156543457094102168 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 116, 95, 101, 113, 95, 116, 114, 117, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__2_value) as *mut crate::leanh::LeanObject,6162781165823963266 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__0_value) as *mut crate::leanh::LeanObject,665796189504554409 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value: crate::leanh::LeanStringObject<96> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 80, 114, 111, 112, 97, 103, 97, 116, 101, 69, 113, 70, 97, 108, 115, 101, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__3_value) as *mut crate::leanh::LeanObject,11397426148428336704 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__5_value) as *mut crate::leanh::LeanObject,17381615769107464045 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__7_value) as *mut crate::leanh::LeanObject,9508759425124742748 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__0_value) as *mut crate::leanh::LeanObject,18346083057132032349 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__2_value) as *mut crate::leanh::LeanObject,2795168870708388791 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__4_value) as *mut crate::leanh::LeanObject,4267366299720466442 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 108, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__6_value) as *mut crate::leanh::LeanObject,3722890380639652857 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 101, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__0_value) as *mut crate::leanh::LeanObject,16327706374038483011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__2_value) as *mut crate::leanh::LeanObject,11594183309238561488 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__0_value) as *mut crate::leanh::LeanObject,5295434444198197881 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 116, 95, 117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__0_value) as *mut crate::leanh::LeanObject,18396075358907067085 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 95, 117, 110, 115, 97, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__0_value) as *mut crate::leanh::LeanObject,13458098464594315830 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 116, 95, 117, 110, 115, 97, 116, 95, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__2_value) as *mut crate::leanh::LeanObject,952555606817756140 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value: crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 79, 114, 100, 101, 114, 46, 109, 107, 85, 110, 115, 97, 116, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 46, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 107, 226, 130, 129, 46, 115, 116, 114, 105, 99, 116, 32, 124, 124, 32, 107, 226, 130, 130, 46, 115, 116, 114, 105, 99, 116, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4555975883093562615 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__2_value) as *mut crate::leanh::LeanObject,1686519415633536789 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2483426619224618075 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Order_mkLePreorderPrefix(
    mut v_declName_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
    mut v_a_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_type_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_a_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2287_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_,
                    v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_,
                );
                if crate::leanh::lean_obj_tag(v___x_2287_) == 0 {
                    v_a_2288_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2303_ = (!crate::leanh::lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v___x_2290_ = v___x_2287_;
                        v_isShared_2291_ = v_isSharedCheck_2303_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2288_);
                        crate::leanh::lean_dec(v___x_2287_);
                        v___x_2290_ = crate::leanh::lean_box(0);
                        v_isShared_2291_ = v_isSharedCheck_2303_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2274_);
                    v_a_2304_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2311_ = (!crate::leanh::lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2311_ == 0 {
                        v___x_2306_ = v___x_2287_;
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2304_);
                        crate::leanh::lean_dec(v___x_2287_);
                        v___x_2306_ = crate::leanh::lean_box(0);
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2292_ = crate::leanh::lean_ctor_get(v_a_2288_, 1);
                crate::leanh::lean_inc_ref(v_type_2292_);
                v_u_2293_ = crate::leanh::lean_ctor_get(v_a_2288_, 2);
                crate::leanh::lean_inc(v_u_2293_);
                v_isPreorderInst_2294_ = crate::leanh::lean_ctor_get(v_a_2288_, 3);
                crate::leanh::lean_inc_ref(v_isPreorderInst_2294_);
                v_leInst_2295_ = crate::leanh::lean_ctor_get(v_a_2288_, 4);
                crate::leanh::lean_inc_ref(v_leInst_2295_);
                crate::leanh::lean_dec(v_a_2288_);
                v___x_2296_ = crate::leanh::lean_box(0);
                v___x_2297_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2297_, 0, v_u_2293_);
                crate::leanh::lean_ctor_set(v___x_2297_, 1, v___x_2296_);
                v___x_2298_ = l_Lean_mkConst(v_declName_2274_, v___x_2297_);
                v___x_2299_ = l_Lean_mkApp3(
                    v___x_2298_,
                    v_type_2292_,
                    v_leInst_2295_,
                    v_isPreorderInst_2294_,
                );
                if v_isShared_2291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2299_);
                    v___x_2301_ = v___x_2290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
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
                    v_reuseFailAlloc_2310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
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
    mut v_declName_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_a_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2323_);
    crate::leanh::lean_dec_ref(v_a_2322_);
    crate::leanh::lean_dec(v_a_2321_);
    crate::leanh::lean_dec_ref(v_a_2320_);
    crate::leanh::lean_dec(v_a_2319_);
    crate::leanh::lean_dec_ref(v_a_2318_);
    crate::leanh::lean_dec(v_a_2317_);
    crate::leanh::lean_dec_ref(v_a_2316_);
    crate::leanh::lean_dec(v_a_2315_);
    crate::leanh::lean_dec(v_a_2314_);
    crate::leanh::lean_dec(v_a_2313_);
    return v_res_2325_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(
    mut v_msg_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lean_instInhabitedExpr;
    v___x_2328_ = lean_panic_fn_borrowed(v___x_2327_, v_msg_2326_);
    return v___x_2328_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__2;
    v___x_2333_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2334_ = crate::leanh::lean_unsigned_to_nat(22);
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
    mut v_declName_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_a_2348_: *mut crate::leanh::LeanObject,
    mut v_a_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v_type_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPartialInst_x3f_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_,
                    v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_,
                );
                if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2372_ = (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2372_ == 0 {
                        v___x_2354_ = v___x_2351_;
                        v_isShared_2355_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2352_);
                        crate::leanh::lean_dec(v___x_2351_);
                        v___x_2354_ = crate::leanh::lean_box(0);
                        v_isShared_2355_ = v_isSharedCheck_2372_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2338_);
                    v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2380_ = (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2375_ = v___x_2351_;
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2373_);
                        crate::leanh::lean_dec(v___x_2351_);
                        v___x_2375_ = crate::leanh::lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2356_ = crate::leanh::lean_ctor_get(v_a_2352_, 1);
                crate::leanh::lean_inc_ref(v_type_2356_);
                v_u_2357_ = crate::leanh::lean_ctor_get(v_a_2352_, 2);
                crate::leanh::lean_inc(v_u_2357_);
                v_leInst_2358_ = crate::leanh::lean_ctor_get(v_a_2352_, 4);
                crate::leanh::lean_inc_ref(v_leInst_2358_);
                v_isPartialInst_x3f_2359_ = crate::leanh::lean_ctor_get(v_a_2352_, 6);
                crate::leanh::lean_inc(v_isPartialInst_x3f_2359_);
                crate::leanh::lean_dec(v_a_2352_);
                v___x_2360_ = crate::leanh::lean_box(0);
                v___x_2361_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2361_, 0, v_u_2357_);
                crate::leanh::lean_ctor_set(v___x_2361_, 1, v___x_2360_);
                v___x_2362_ = l_Lean_mkConst(v_declName_2338_, v___x_2361_);
                if crate::leanh::lean_obj_tag(v_isPartialInst_x3f_2359_) == 0 {
                    v___x_2369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2370_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2369_);
                    v___y_2364_ = v___x_2370_;
                    state = 2;
                    continue;
                } else {
                    v_val_2371_ = crate::leanh::lean_ctor_get(v_isPartialInst_x3f_2359_, 0);
                    crate::leanh::lean_inc(v_val_2371_);
                    crate::leanh::lean_dec_ref_known(v_isPartialInst_x3f_2359_, 1);
                    v___y_2364_ = v_val_2371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2365_ = l_Lean_mkApp3(v___x_2362_, v_type_2356_, v_leInst_2358_, v___y_2364_);
                if v_isShared_2355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
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
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
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
    mut v_declName_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
    mut v_a_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2392_);
    crate::leanh::lean_dec_ref(v_a_2391_);
    crate::leanh::lean_dec(v_a_2390_);
    crate::leanh::lean_dec_ref(v_a_2389_);
    crate::leanh::lean_dec(v_a_2388_);
    crate::leanh::lean_dec_ref(v_a_2387_);
    crate::leanh::lean_dec(v_a_2386_);
    crate::leanh::lean_dec_ref(v_a_2385_);
    crate::leanh::lean_dec(v_a_2384_);
    crate::leanh::lean_dec(v_a_2383_);
    crate::leanh::lean_dec(v_a_2382_);
    return v_res_2394_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(
    mut v_declName_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v_type_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2436_: u8 = 0;
    let mut v_a_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2408_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_,
                    v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_,
                );
                if crate::leanh::lean_obj_tag(v___x_2408_) == 0 {
                    v_a_2409_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                    v_isSharedCheck_2436_ = (!crate::leanh::lean_is_exclusive(v___x_2408_)) as u8;
                    if v_isSharedCheck_2436_ == 0 {
                        v___x_2411_ = v___x_2408_;
                        v_isShared_2412_ = v_isSharedCheck_2436_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2409_);
                        crate::leanh::lean_dec(v___x_2408_);
                        v___x_2411_ = crate::leanh::lean_box(0);
                        v_isShared_2412_ = v_isSharedCheck_2436_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2395_);
                    v_a_2437_ = crate::leanh::lean_ctor_get(v___x_2408_, 0);
                    v_isSharedCheck_2444_ = (!crate::leanh::lean_is_exclusive(v___x_2408_)) as u8;
                    if v_isSharedCheck_2444_ == 0 {
                        v___x_2439_ = v___x_2408_;
                        v_isShared_2440_ = v_isSharedCheck_2444_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2437_);
                        crate::leanh::lean_dec(v___x_2408_);
                        v___x_2439_ = crate::leanh::lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2444_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2413_ = crate::leanh::lean_ctor_get(v_a_2409_, 1);
                crate::leanh::lean_inc_ref(v_type_2413_);
                v_u_2414_ = crate::leanh::lean_ctor_get(v_a_2409_, 2);
                crate::leanh::lean_inc(v_u_2414_);
                v_leInst_2415_ = crate::leanh::lean_ctor_get(v_a_2409_, 4);
                crate::leanh::lean_inc_ref(v_leInst_2415_);
                v_ltInst_x3f_2416_ = crate::leanh::lean_ctor_get(v_a_2409_, 5);
                crate::leanh::lean_inc(v_ltInst_x3f_2416_);
                v_lawfulOrderLTInst_x3f_2417_ = crate::leanh::lean_ctor_get(v_a_2409_, 8);
                crate::leanh::lean_inc(v_lawfulOrderLTInst_x3f_2417_);
                crate::leanh::lean_dec(v_a_2409_);
                v___x_2418_ = crate::leanh::lean_box(0);
                v___x_2419_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2419_, 0, v_u_2414_);
                crate::leanh::lean_ctor_set(v___x_2419_, 1, v___x_2418_);
                v___x_2420_ = l_Lean_mkConst(v_declName_2395_, v___x_2419_);
                if crate::leanh::lean_obj_tag(v_ltInst_x3f_2416_) == 0 {
                    v___x_2433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2434_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2433_);
                    v___y_2429_ = v___x_2434_;
                    state = 4;
                    continue;
                } else {
                    v_val_2435_ = crate::leanh::lean_ctor_get(v_ltInst_x3f_2416_, 0);
                    crate::leanh::lean_inc(v_val_2435_);
                    crate::leanh::lean_dec_ref_known(v_ltInst_x3f_2416_, 1);
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
                    crate::leanh::lean_ctor_set(v___x_2411_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2411_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2426_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_lawfulOrderLTInst_x3f_2417_) == 0 {
                    v___x_2430_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2431_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2430_);
                    v___y_2422_ = v___y_2429_;
                    v___y_2423_ = v___x_2431_;
                    state = 2;
                    continue;
                } else {
                    v_val_2432_ = crate::leanh::lean_ctor_get(v_lawfulOrderLTInst_x3f_2417_, 0);
                    crate::leanh::lean_inc(v_val_2432_);
                    crate::leanh::lean_dec_ref_known(v_lawfulOrderLTInst_x3f_2417_, 1);
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
                    v_reuseFailAlloc_2443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
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
    mut v_declName_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2456_);
    crate::leanh::lean_dec_ref(v_a_2455_);
    crate::leanh::lean_dec(v_a_2454_);
    crate::leanh::lean_dec_ref(v_a_2453_);
    crate::leanh::lean_dec(v_a_2452_);
    crate::leanh::lean_dec_ref(v_a_2451_);
    crate::leanh::lean_dec(v_a_2450_);
    crate::leanh::lean_dec_ref(v_a_2449_);
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec(v_a_2447_);
    crate::leanh::lean_dec(v_a_2446_);
    return v_res_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(
    mut v_declName_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v_isPreorderInst_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_a_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2472_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_,
                    v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_,
                );
                if crate::leanh::lean_obj_tag(v___x_2472_) == 0 {
                    v_a_2473_ = crate::leanh::lean_ctor_get(v___x_2472_, 0);
                    crate::leanh::lean_inc(v_a_2473_);
                    crate::leanh::lean_dec_ref_known(v___x_2472_, 1);
                    v___x_2474_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if crate::leanh::lean_obj_tag(v___x_2474_) == 0 {
                        v_a_2475_ = crate::leanh::lean_ctor_get(v___x_2474_, 0);
                        v_isSharedCheck_2484_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2474_)) as u8;
                        if v_isSharedCheck_2484_ == 0 {
                            v___x_2477_ = v___x_2474_;
                            v_isShared_2478_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2475_);
                            crate::leanh::lean_dec(v___x_2474_);
                            v___x_2477_ = crate::leanh::lean_box(0);
                            v_isShared_2478_ = v_isSharedCheck_2484_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2473_);
                        return v___x_2474_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2459_);
                    v_a_2485_ = crate::leanh::lean_ctor_get(v___x_2472_, 0);
                    v_isSharedCheck_2492_ = (!crate::leanh::lean_is_exclusive(v___x_2472_)) as u8;
                    if v_isSharedCheck_2492_ == 0 {
                        v___x_2487_ = v___x_2472_;
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2485_);
                        crate::leanh::lean_dec(v___x_2472_);
                        v___x_2487_ = crate::leanh::lean_box(0);
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_isPreorderInst_2479_ = crate::leanh::lean_ctor_get(v_a_2473_, 3);
                crate::leanh::lean_inc_ref(v_isPreorderInst_2479_);
                crate::leanh::lean_dec(v_a_2473_);
                v___x_2480_ = l_Lean_Expr_app___override(v_a_2475_, v_isPreorderInst_2479_);
                if v_isShared_2478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
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
                    v_reuseFailAlloc_2491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
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
    mut v_declName_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
    crate::leanh::lean_dec(v_a_2504_);
    crate::leanh::lean_dec_ref(v_a_2503_);
    crate::leanh::lean_dec(v_a_2502_);
    crate::leanh::lean_dec_ref(v_a_2501_);
    crate::leanh::lean_dec(v_a_2500_);
    crate::leanh::lean_dec_ref(v_a_2499_);
    crate::leanh::lean_dec(v_a_2498_);
    crate::leanh::lean_dec_ref(v_a_2497_);
    crate::leanh::lean_dec(v_a_2496_);
    crate::leanh::lean_dec(v_a_2495_);
    crate::leanh::lean_dec(v_a_2494_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(
    mut v_declName_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_a_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___y_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearPreInst_x3f_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v_a_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2520_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_,
                    v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_,
                );
                if crate::leanh::lean_obj_tag(v___x_2520_) == 0 {
                    v_a_2521_ = crate::leanh::lean_ctor_get(v___x_2520_, 0);
                    crate::leanh::lean_inc(v_a_2521_);
                    crate::leanh::lean_dec_ref_known(v___x_2520_, 1);
                    v___x_2522_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v_declName_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
                    if crate::leanh::lean_obj_tag(v___x_2522_) == 0 {
                        v_a_2523_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                        v_isSharedCheck_2537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2522_)) as u8;
                        if v_isSharedCheck_2537_ == 0 {
                            v___x_2525_ = v___x_2522_;
                            v_isShared_2526_ = v_isSharedCheck_2537_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2523_);
                            crate::leanh::lean_dec(v___x_2522_);
                            v___x_2525_ = crate::leanh::lean_box(0);
                            v_isShared_2526_ = v_isSharedCheck_2537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2521_);
                        return v___x_2522_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2507_);
                    v_a_2538_ = crate::leanh::lean_ctor_get(v___x_2520_, 0);
                    v_isSharedCheck_2545_ = (!crate::leanh::lean_is_exclusive(v___x_2520_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v___x_2540_ = v___x_2520_;
                        v_isShared_2541_ = v_isSharedCheck_2545_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2538_);
                        crate::leanh::lean_dec(v___x_2520_);
                        v___x_2540_ = crate::leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2545_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearPreInst_x3f_2533_ = crate::leanh::lean_ctor_get(v_a_2521_, 7);
                crate::leanh::lean_inc(v_isLinearPreInst_x3f_2533_);
                crate::leanh::lean_dec(v_a_2521_);
                if crate::leanh::lean_obj_tag(v_isLinearPreInst_x3f_2533_) == 0 {
                    v___x_2534_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2535_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2534_);
                    v___y_2528_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_val_2536_ = crate::leanh::lean_ctor_get(v_isLinearPreInst_x3f_2533_, 0);
                    crate::leanh::lean_inc(v_val_2536_);
                    crate::leanh::lean_dec_ref_known(v_isLinearPreInst_x3f_2533_, 1);
                    v___y_2528_ = v_val_2536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2529_ = l_Lean_Expr_app___override(v_a_2523_, v___y_2528_);
                if v_isShared_2526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2525_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
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
                    v_reuseFailAlloc_2544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
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
    mut v_declName_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
    mut v_a_2551_: *mut crate::leanh::LeanObject,
    mut v_a_2552_: *mut crate::leanh::LeanObject,
    mut v_a_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
    mut v_a_2555_: *mut crate::leanh::LeanObject,
    mut v_a_2556_: *mut crate::leanh::LeanObject,
    mut v_a_2557_: *mut crate::leanh::LeanObject,
    mut v_a_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2557_);
    crate::leanh::lean_dec_ref(v_a_2556_);
    crate::leanh::lean_dec(v_a_2555_);
    crate::leanh::lean_dec_ref(v_a_2554_);
    crate::leanh::lean_dec(v_a_2553_);
    crate::leanh::lean_dec_ref(v_a_2552_);
    crate::leanh::lean_dec(v_a_2551_);
    crate::leanh::lean_dec_ref(v_a_2550_);
    crate::leanh::lean_dec(v_a_2549_);
    crate::leanh::lean_dec(v_a_2548_);
    crate::leanh::lean_dec(v_a_2547_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLeLinearPrefix(
    mut v_declName_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
    mut v_a_2563_: *mut crate::leanh::LeanObject,
    mut v_a_2564_: *mut crate::leanh::LeanObject,
    mut v_a_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
    mut v_a_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v_type_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearPreInst_x3f_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2573_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_,
                    v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_,
                );
                if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                    v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2594_ = (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2594_ == 0 {
                        v___x_2576_ = v___x_2573_;
                        v_isShared_2577_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2574_);
                        crate::leanh::lean_dec(v___x_2573_);
                        v___x_2576_ = crate::leanh::lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2594_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2560_);
                    v_a_2595_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2602_ = (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2597_ = v___x_2573_;
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2595_);
                        crate::leanh::lean_dec(v___x_2573_);
                        v___x_2597_ = crate::leanh::lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2602_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_type_2578_ = crate::leanh::lean_ctor_get(v_a_2574_, 1);
                crate::leanh::lean_inc_ref(v_type_2578_);
                v_u_2579_ = crate::leanh::lean_ctor_get(v_a_2574_, 2);
                crate::leanh::lean_inc(v_u_2579_);
                v_leInst_2580_ = crate::leanh::lean_ctor_get(v_a_2574_, 4);
                crate::leanh::lean_inc_ref(v_leInst_2580_);
                v_isLinearPreInst_x3f_2581_ = crate::leanh::lean_ctor_get(v_a_2574_, 7);
                crate::leanh::lean_inc(v_isLinearPreInst_x3f_2581_);
                crate::leanh::lean_dec(v_a_2574_);
                v___x_2582_ = crate::leanh::lean_box(0);
                v___x_2583_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2583_, 0, v_u_2579_);
                crate::leanh::lean_ctor_set(v___x_2583_, 1, v___x_2582_);
                v___x_2584_ = l_Lean_mkConst(v_declName_2560_, v___x_2583_);
                if crate::leanh::lean_obj_tag(v_isLinearPreInst_x3f_2581_) == 0 {
                    v___x_2591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2592_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2591_);
                    v___y_2586_ = v___x_2592_;
                    state = 2;
                    continue;
                } else {
                    v_val_2593_ = crate::leanh::lean_ctor_get(v_isLinearPreInst_x3f_2581_, 0);
                    crate::leanh::lean_inc(v_val_2593_);
                    crate::leanh::lean_dec_ref_known(v_isLinearPreInst_x3f_2581_, 1);
                    v___y_2586_ = v_val_2593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2587_ = l_Lean_mkApp3(v___x_2584_, v_type_2578_, v_leInst_2580_, v___y_2586_);
                if v_isShared_2577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2576_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
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
                    v_reuseFailAlloc_2601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
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
    mut v_declName_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2614_);
    crate::leanh::lean_dec_ref(v_a_2613_);
    crate::leanh::lean_dec(v_a_2612_);
    crate::leanh::lean_dec_ref(v_a_2611_);
    crate::leanh::lean_dec(v_a_2610_);
    crate::leanh::lean_dec_ref(v_a_2609_);
    crate::leanh::lean_dec(v_a_2608_);
    crate::leanh::lean_dec_ref(v_a_2607_);
    crate::leanh::lean_dec(v_a_2606_);
    crate::leanh::lean_dec(v_a_2605_);
    crate::leanh::lean_dec(v_a_2604_);
    return v_res_2616_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkOrdRingPrefix(
    mut v_declName_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v___y_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_a_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_,
                    v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_,
                );
                if crate::leanh::lean_obj_tag(v___x_2630_) == 0 {
                    v_a_2631_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                    crate::leanh::lean_inc(v_a_2631_);
                    crate::leanh::lean_dec_ref_known(v___x_2630_, 1);
                    v___x_2632_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v_declName_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
                    if crate::leanh::lean_obj_tag(v___x_2632_) == 0 {
                        v_a_2633_ = crate::leanh::lean_ctor_get(v___x_2632_, 0);
                        v_isSharedCheck_2654_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2632_)) as u8;
                        if v_isSharedCheck_2654_ == 0 {
                            v___x_2635_ = v___x_2632_;
                            v_isShared_2636_ = v_isSharedCheck_2654_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2633_);
                            crate::leanh::lean_dec(v___x_2632_);
                            v___x_2635_ = crate::leanh::lean_box(0);
                            v_isShared_2636_ = v_isSharedCheck_2654_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2631_);
                        return v___x_2632_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2617_);
                    v_a_2655_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                    v_isSharedCheck_2662_ = (!crate::leanh::lean_is_exclusive(v___x_2630_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2657_ = v___x_2630_;
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2655_);
                        crate::leanh::lean_dec(v___x_2630_);
                        v___x_2657_ = crate::leanh::lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringInst_x3f_2644_ = crate::leanh::lean_ctor_get(v_a_2631_, 10);
                crate::leanh::lean_inc(v_ringInst_x3f_2644_);
                v_orderedRingInst_x3f_2645_ = crate::leanh::lean_ctor_get(v_a_2631_, 11);
                crate::leanh::lean_inc(v_orderedRingInst_x3f_2645_);
                crate::leanh::lean_dec(v_a_2631_);
                if crate::leanh::lean_obj_tag(v_ringInst_x3f_2644_) == 0 {
                    v___x_2651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2652_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2651_);
                    v___y_2647_ = v___x_2652_;
                    state = 4;
                    continue;
                } else {
                    v_val_2653_ = crate::leanh::lean_ctor_get(v_ringInst_x3f_2644_, 0);
                    crate::leanh::lean_inc(v_val_2653_);
                    crate::leanh::lean_dec_ref_known(v_ringInst_x3f_2644_, 1);
                    v___y_2647_ = v_val_2653_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = l_Lean_mkAppB(v_a_2633_, v___y_2638_, v___y_2639_);
                if v_isShared_2636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2640_);
                    v___x_2642_ = v___x_2635_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
                    v___x_2642_ = v_reuseFailAlloc_2643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2642_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_orderedRingInst_x3f_2645_) == 0 {
                    v___x_2648_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2649_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2648_);
                    v___y_2638_ = v___y_2647_;
                    v___y_2639_ = v___x_2649_;
                    state = 2;
                    continue;
                } else {
                    v_val_2650_ = crate::leanh::lean_ctor_get(v_orderedRingInst_x3f_2645_, 0);
                    crate::leanh::lean_inc(v_val_2650_);
                    crate::leanh::lean_dec_ref_known(v_orderedRingInst_x3f_2645_, 1);
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
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
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
    mut v_declName_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
    mut v_a_2670_: *mut crate::leanh::LeanObject,
    mut v_a_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2674_);
    crate::leanh::lean_dec_ref(v_a_2673_);
    crate::leanh::lean_dec(v_a_2672_);
    crate::leanh::lean_dec_ref(v_a_2671_);
    crate::leanh::lean_dec(v_a_2670_);
    crate::leanh::lean_dec_ref(v_a_2669_);
    crate::leanh::lean_dec(v_a_2668_);
    crate::leanh::lean_dec_ref(v_a_2667_);
    crate::leanh::lean_dec(v_a_2666_);
    crate::leanh::lean_dec(v_a_2665_);
    crate::leanh::lean_dec(v_a_2664_);
    return v_res_2676_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(
    mut v_declName_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
    mut v_a_2683_: *mut crate::leanh::LeanObject,
    mut v_a_2684_: *mut crate::leanh::LeanObject,
    mut v_a_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
    mut v_a_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___y_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_a_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2690_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_,
                    v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_,
                );
                if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                    v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                    crate::leanh::lean_inc(v_a_2691_);
                    crate::leanh::lean_dec_ref_known(v___x_2690_, 1);
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
                    if crate::leanh::lean_obj_tag(v___x_2692_) == 0 {
                        v_a_2693_ = crate::leanh::lean_ctor_get(v___x_2692_, 0);
                        v_isSharedCheck_2714_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2692_)) as u8;
                        if v_isSharedCheck_2714_ == 0 {
                            v___x_2695_ = v___x_2692_;
                            v_isShared_2696_ = v_isSharedCheck_2714_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2693_);
                            crate::leanh::lean_dec(v___x_2692_);
                            v___x_2695_ = crate::leanh::lean_box(0);
                            v_isShared_2696_ = v_isSharedCheck_2714_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2691_);
                        return v___x_2692_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2677_);
                    v_a_2715_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                    v_isSharedCheck_2722_ = (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v___x_2717_ = v___x_2690_;
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2715_);
                        crate::leanh::lean_dec(v___x_2690_);
                        v___x_2717_ = crate::leanh::lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringInst_x3f_2704_ = crate::leanh::lean_ctor_get(v_a_2691_, 10);
                crate::leanh::lean_inc(v_ringInst_x3f_2704_);
                v_orderedRingInst_x3f_2705_ = crate::leanh::lean_ctor_get(v_a_2691_, 11);
                crate::leanh::lean_inc(v_orderedRingInst_x3f_2705_);
                crate::leanh::lean_dec(v_a_2691_);
                if crate::leanh::lean_obj_tag(v_ringInst_x3f_2704_) == 0 {
                    v___x_2711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2712_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2711_);
                    v___y_2707_ = v___x_2712_;
                    state = 4;
                    continue;
                } else {
                    v_val_2713_ = crate::leanh::lean_ctor_get(v_ringInst_x3f_2704_, 0);
                    crate::leanh::lean_inc(v_val_2713_);
                    crate::leanh::lean_dec_ref_known(v_ringInst_x3f_2704_, 1);
                    v___y_2707_ = v_val_2713_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2700_ = l_Lean_mkAppB(v_a_2693_, v___y_2698_, v___y_2699_);
                if v_isShared_2696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2700_);
                    v___x_2702_ = v___x_2695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2702_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_orderedRingInst_x3f_2705_) == 0 {
                    v___x_2708_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_2709_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_2708_);
                    v___y_2698_ = v___y_2707_;
                    v___y_2699_ = v___x_2709_;
                    state = 2;
                    continue;
                } else {
                    v_val_2710_ = crate::leanh::lean_ctor_get(v_orderedRingInst_x3f_2705_, 0);
                    crate::leanh::lean_inc(v_val_2710_);
                    crate::leanh::lean_dec_ref_known(v_orderedRingInst_x3f_2705_, 1);
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
                    v_reuseFailAlloc_2721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
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
    mut v_declName_2723_: *mut crate::leanh::LeanObject,
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
    mut v_a_2734_: *mut crate::leanh::LeanObject,
    mut v_a_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2734_);
    crate::leanh::lean_dec_ref(v_a_2733_);
    crate::leanh::lean_dec(v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    crate::leanh::lean_dec(v_a_2726_);
    crate::leanh::lean_dec(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    return v_res_2736_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(
    mut v_u_2764_: *mut crate::leanh::LeanObject,
    mut v_v_2765_: *mut crate::leanh::LeanObject,
    mut v_w_2766_: *mut crate::leanh::LeanObject,
    mut v_strict_u2081_2767_: u8,
    mut v_strict_u2082_2768_: u8,
    mut v_h_u2081_2769_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_2770_: *mut crate::leanh::LeanObject,
    mut v_a_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_a_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: *mut crate::leanh::LeanObject,
    mut v_a_2776_: *mut crate::leanh::LeanObject,
    mut v_a_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                        if crate::leanh::lean_obj_tag(v___x_2788_) == 0 {
                            v_a_2789_ = crate::leanh::lean_ctor_get(v___x_2788_, 0);
                            crate::leanh::lean_inc(v_a_2789_);
                            crate::leanh::lean_dec_ref_known(v___x_2788_, 1);
                            v_h_2784_ = v_a_2789_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2770_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2769_);
                            crate::leanh::lean_dec_ref(v_w_2766_);
                            crate::leanh::lean_dec_ref(v_v_2765_);
                            crate::leanh::lean_dec_ref(v_u_2764_);
                            return v___x_2788_;
                        }
                    } else {
                        v___x_2790_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__6;
                        v___x_2791_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2790_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if crate::leanh::lean_obj_tag(v___x_2791_) == 0 {
                            v_a_2792_ = crate::leanh::lean_ctor_get(v___x_2791_, 0);
                            crate::leanh::lean_inc(v_a_2792_);
                            crate::leanh::lean_dec_ref_known(v___x_2791_, 1);
                            v_h_2784_ = v_a_2792_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2770_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2769_);
                            crate::leanh::lean_dec_ref(v_w_2766_);
                            crate::leanh::lean_dec_ref(v_v_2765_);
                            crate::leanh::lean_dec_ref(v_u_2764_);
                            return v___x_2791_;
                        }
                    }
                } else {
                    if v_strict_u2082_2768_ == 0 {
                        v___x_2793_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__8;
                        v___x_2794_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2793_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if crate::leanh::lean_obj_tag(v___x_2794_) == 0 {
                            v_a_2795_ = crate::leanh::lean_ctor_get(v___x_2794_, 0);
                            crate::leanh::lean_inc(v_a_2795_);
                            crate::leanh::lean_dec_ref_known(v___x_2794_, 1);
                            v_h_2784_ = v_a_2795_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2770_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2769_);
                            crate::leanh::lean_dec_ref(v_w_2766_);
                            crate::leanh::lean_dec_ref(v_v_2765_);
                            crate::leanh::lean_dec_ref(v_u_2764_);
                            return v___x_2794_;
                        }
                    } else {
                        v___x_2796_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___closed__10;
                        v___x_2797_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_2796_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
                        if crate::leanh::lean_obj_tag(v___x_2797_) == 0 {
                            v_a_2798_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
                            crate::leanh::lean_inc(v_a_2798_);
                            crate::leanh::lean_dec_ref_known(v___x_2797_, 1);
                            v_h_2784_ = v_a_2798_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2770_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2769_);
                            crate::leanh::lean_dec_ref(v_w_2766_);
                            crate::leanh::lean_dec_ref(v_v_2765_);
                            crate::leanh::lean_dec_ref(v_u_2764_);
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
                v___x_2786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2786_, 0, v___x_2785_);
                return v___x_2786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_2799_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_2800_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_w_2801_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_strict_u2081_2802_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_strict_u2082_2803_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_h_u2081_2804_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_h_u2082_2805_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_2806_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_2807_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_2808_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_2809_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_2810_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_2811_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_2812_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_2813_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_2814_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_2815_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_2816_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_2817_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_strict_u2081_boxed_2818_: u8 = 0;
    let mut v_strict_u2082_boxed_2819_: u8 = 0;
    let mut v_res_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_strict_u2081_boxed_2818_ = (crate::leanh::lean_unbox(v_strict_u2081_2802_) as u8);
    v_strict_u2082_boxed_2819_ = (crate::leanh::lean_unbox(v_strict_u2082_2803_) as u8);
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
    crate::leanh::lean_dec(v_a_2816_);
    crate::leanh::lean_dec_ref(v_a_2815_);
    crate::leanh::lean_dec(v_a_2814_);
    crate::leanh::lean_dec_ref(v_a_2813_);
    crate::leanh::lean_dec(v_a_2812_);
    crate::leanh::lean_dec_ref(v_a_2811_);
    crate::leanh::lean_dec(v_a_2810_);
    crate::leanh::lean_dec_ref(v_a_2809_);
    crate::leanh::lean_dec(v_a_2808_);
    crate::leanh::lean_dec(v_a_2807_);
    crate::leanh::lean_dec(v_a_2806_);
    return v_res_2820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(
    mut v_xs_2821_: *mut crate::leanh::LeanObject,
    mut v_i_2822_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    v_size_2823_ = crate::leanh::lean_ctor_get(v_xs_2821_, 2);
    v___x_2824_ = lean_nat_dec_lt(v_i_2822_, v_size_2823_);
    return v___x_2824_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0___boxed(
    mut v_xs_2825_: *mut crate::leanh::LeanObject,
    mut v_i_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: u8 = 0;
    let mut v_r_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___lam__0(v_xs_2825_, v_i_2826_);
    crate::leanh::lean_dec(v_i_2826_);
    crate::leanh::lean_dec_ref(v_xs_2825_);
    v_r_2828_ = crate::leanh::lean_box((v_res_2827_) as usize);
    return v_r_2828_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2830_ = lean_nat_to_int(v___x_2829_);
    return v___x_2830_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(
    mut v_p_u2081_2831_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2832_: *mut crate::leanh::LeanObject,
    mut v_v_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_a_2836_: *mut crate::leanh::LeanObject,
    mut v_a_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___y_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2855_: u8 = 0;
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_2862_: u8 = 0;
    let mut v_w_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_2865_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_nodes_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u8 = 0;
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_w_2846_ = crate::leanh::lean_ctor_get(v_p_u2081_2831_, 0);
                v_k_2847_ = crate::leanh::lean_ctor_get(v_p_u2081_2831_, 1);
                v_proof_2848_ = crate::leanh::lean_ctor_get(v_p_u2081_2831_, 2);
                v_isSharedCheck_2907_ = (!crate::leanh::lean_is_exclusive(v_p_u2081_2831_)) as u8;
                if v_isSharedCheck_2907_ == 0 {
                    v___x_2850_ = v_p_u2081_2831_;
                    v_isShared_2851_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_2848_);
                    crate::leanh::lean_inc(v_k_2847_);
                    crate::leanh::lean_inc(v_w_2846_);
                    crate::leanh::lean_dec(v_p_u2081_2831_);
                    v___x_2850_ = crate::leanh::lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_k_2861_ = crate::leanh::lean_ctor_get(v_p_u2082_2832_, 1);
                crate::leanh::lean_inc_ref(v_k_2861_);
                v_strict_2862_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_2847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_k_2847_);
                v_w_2863_ = crate::leanh::lean_ctor_get(v_p_u2082_2832_, 0);
                crate::leanh::lean_inc(v_w_2863_);
                v_proof_2864_ = crate::leanh::lean_ctor_get(v_p_u2082_2832_, 2);
                crate::leanh::lean_inc_ref(v_proof_2864_);
                crate::leanh::lean_dec_ref(v_p_u2082_2832_);
                v_strict_2865_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_2861_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_k_2861_);
                v___x_2866_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_,
                    v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_,
                );
                if crate::leanh::lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    crate::leanh::lean_inc(v_a_2867_);
                    crate::leanh::lean_dec_ref_known(v___x_2866_, 1);
                    v_nodes_2883_ = crate::leanh::lean_ctor_get(v_a_2867_, 14);
                    crate::leanh::lean_inc_ref(v_nodes_2883_);
                    crate::leanh::lean_dec(v_a_2867_);
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
                    crate::leanh::lean_dec_ref(v_proof_2864_);
                    crate::leanh::lean_dec(v_w_2863_);
                    crate::leanh::lean_del_object(v___x_2850_);
                    crate::leanh::lean_dec_ref(v_proof_2848_);
                    crate::leanh::lean_dec(v_w_2846_);
                    v_a_2899_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2906_ = (!crate::leanh::lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2906_ == 0 {
                        v___x_2901_ = v___x_2866_;
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2899_);
                        crate::leanh::lean_dec(v___x_2866_);
                        v___x_2901_ = crate::leanh::lean_box(0);
                        v_isShared_2902_ = v_isSharedCheck_2906_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_2853_);
                v___x_2856_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2856_, 0, v___y_2853_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_2855_,
                );
                if v_isShared_2851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2850_, 2, v___y_2854_);
                    crate::leanh::lean_ctor_set(v___x_2850_, 1, v___x_2856_);
                    v___x_2858_ = v___x_2850_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_w_2846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 2, v___y_2854_);
                    v___x_2858_ = v_reuseFailAlloc_2860_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2858_);
                return v___x_2859_;
            }
            4 => {
                v___x_2872_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v___y_2870_, v___y_2869_, v___y_2871_, v_strict_2862_, v_strict_2865_, v_proof_2848_, v_proof_2864_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
                if crate::leanh::lean_obj_tag(v___x_2872_) == 0 {
                    v_a_2873_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                    crate::leanh::lean_inc(v_a_2873_);
                    crate::leanh::lean_dec_ref_known(v___x_2872_, 1);
                    v___x_2874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
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
                    crate::leanh::lean_del_object(v___x_2850_);
                    crate::leanh::lean_dec(v_w_2846_);
                    v_a_2875_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                    v_isSharedCheck_2882_ = (!crate::leanh::lean_is_exclusive(v___x_2872_)) as u8;
                    if v_isSharedCheck_2882_ == 0 {
                        v___x_2877_ = v___x_2872_;
                        v_isShared_2878_ = v_isSharedCheck_2882_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2875_);
                        crate::leanh::lean_dec(v___x_2872_);
                        v___x_2877_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
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
                    crate::leanh::lean_dec_ref(v_nodes_2883_);
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
                    crate::leanh::lean_dec_ref(v_nodes_2883_);
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
                    crate::leanh::lean_dec(v_w_2863_);
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
                    crate::leanh::lean_dec(v_w_2863_);
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
                    v_reuseFailAlloc_2905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
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
    mut v_p_u2081_2908_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_2909_: *mut crate::leanh::LeanObject,
    mut v_v_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
    mut v_a_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2921_);
    crate::leanh::lean_dec_ref(v_a_2920_);
    crate::leanh::lean_dec(v_a_2919_);
    crate::leanh::lean_dec_ref(v_a_2918_);
    crate::leanh::lean_dec(v_a_2917_);
    crate::leanh::lean_dec_ref(v_a_2916_);
    crate::leanh::lean_dec(v_a_2915_);
    crate::leanh::lean_dec_ref(v_a_2914_);
    crate::leanh::lean_dec(v_a_2913_);
    crate::leanh::lean_dec(v_a_2912_);
    crate::leanh::lean_dec(v_a_2911_);
    crate::leanh::lean_dec(v_v_2910_);
    return v_res_2923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2930_ = l_Lean_Level_ofNat(v___x_2929_);
    return v___x_2930_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2931_ = crate::leanh::lean_box(0);
    v___x_2932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__3);
    v___x_2933_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2932_);
    crate::leanh::lean_ctor_set(v___x_2933_, 1, v___x_2931_);
    return v___x_2933_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__4);
    v___x_2935_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__2;
    v___x_2936_ = l_Lean_Expr_const___override(v___x_2935_, v___x_2934_);
    return v___x_2936_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = crate::leanh::lean_box(0);
    v___x_2941_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__7;
    v___x_2942_ = l_Lean_Expr_const___override(v___x_2941_, v___x_2940_);
    return v___x_2942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = crate::leanh::lean_box(0);
    v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__10;
    v___x_2949_ = l_Lean_Expr_const___override(v___x_2948_, v___x_2947_);
    return v___x_2949_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(
    mut v_u_2974_: *mut crate::leanh::LeanObject,
    mut v_v_2975_: *mut crate::leanh::LeanObject,
    mut v_w_2976_: *mut crate::leanh::LeanObject,
    mut v_k_u2081_2977_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_2978_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_2979_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
    mut v_a_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_a_2984_: *mut crate::leanh::LeanObject,
    mut v_a_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3035_: u8 = 0;
    let mut v_h_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3051_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3058_: u8 = 0;
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3034_ = crate::leanh::lean_ctor_get(v_k_u2081_2977_, 0);
                v_strict_3035_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_u2081_2977_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_3035_ == 0 {
                    v_strict_3051_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_u2082_2978_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                        if crate::leanh::lean_obj_tag(v___x_3053_) == 0 {
                            v_a_3054_ = crate::leanh::lean_ctor_get(v___x_3053_, 0);
                            crate::leanh::lean_inc(v_a_3054_);
                            crate::leanh::lean_dec_ref_known(v___x_3053_, 1);
                            v_h_3037_ = v_a_3054_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2980_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2979_);
                            crate::leanh::lean_dec_ref(v_w_2976_);
                            crate::leanh::lean_dec_ref(v_v_2975_);
                            crate::leanh::lean_dec_ref(v_u_2974_);
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
                        if crate::leanh::lean_obj_tag(v___x_3056_) == 0 {
                            v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                            crate::leanh::lean_inc(v_a_3057_);
                            crate::leanh::lean_dec_ref_known(v___x_3056_, 1);
                            v_h_3037_ = v_a_3057_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2980_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2979_);
                            crate::leanh::lean_dec_ref(v_w_2976_);
                            crate::leanh::lean_dec_ref(v_v_2975_);
                            crate::leanh::lean_dec_ref(v_u_2974_);
                            return v___x_3056_;
                        }
                    }
                } else {
                    v_strict_3058_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_u2082_2978_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                        if crate::leanh::lean_obj_tag(v___x_3060_) == 0 {
                            v_a_3061_ = crate::leanh::lean_ctor_get(v___x_3060_, 0);
                            crate::leanh::lean_inc(v_a_3061_);
                            crate::leanh::lean_dec_ref_known(v___x_3060_, 1);
                            v_h_3037_ = v_a_3061_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2980_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2979_);
                            crate::leanh::lean_dec_ref(v_w_2976_);
                            crate::leanh::lean_dec_ref(v_v_2975_);
                            crate::leanh::lean_dec_ref(v_u_2974_);
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
                        if crate::leanh::lean_obj_tag(v___x_3063_) == 0 {
                            v_a_3064_ = crate::leanh::lean_ctor_get(v___x_3063_, 0);
                            crate::leanh::lean_inc(v_a_3064_);
                            crate::leanh::lean_dec_ref_known(v___x_3063_, 1);
                            v_h_3037_ = v_a_3064_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_u2082_2980_);
                            crate::leanh::lean_dec_ref(v_h_u2081_2979_);
                            crate::leanh::lean_dec_ref(v_w_2976_);
                            crate::leanh::lean_dec_ref(v_v_2975_);
                            crate::leanh::lean_dec_ref(v_u_2974_);
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
                v___x_3001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_3000_);
                return v___x_3001_;
            }
            2 => {
                v___x_3007_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3008_ = lean_int_dec_le(v___x_3007_, v___y_3004_);
                if v___x_3008_ == 0 {
                    v___x_3009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3012_ = lean_int_neg(v___y_3004_);
                    crate::leanh::lean_dec(v___y_3004_);
                    v___x_3013_ = l_Int_toNat(v___x_3012_);
                    crate::leanh::lean_dec(v___x_3012_);
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
                    crate::leanh::lean_dec(v___y_3004_);
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
                v___x_3023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3024_ = lean_int_dec_le(v___x_3023_, v___y_3021_);
                if v___x_3024_ == 0 {
                    v___x_3025_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3027_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3028_ = lean_int_neg(v___y_3021_);
                    v___x_3029_ = l_Int_toNat(v___x_3028_);
                    crate::leanh::lean_dec(v___x_3028_);
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
                v_k_3038_ = crate::leanh::lean_ctor_get(v_k_u2082_2978_, 0);
                v_k_3039_ = lean_int_add(v_k_3034_, v_k_3038_);
                v___x_3040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3041_ = lean_int_dec_le(v___x_3040_, v_k_3034_);
                if v___x_3041_ == 0 {
                    v___x_3042_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3045_ = lean_int_neg(v_k_3034_);
                    v___x_3046_ = l_Int_toNat(v___x_3045_);
                    crate::leanh::lean_dec(v___x_3045_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3065_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3066_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_w_3067_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_k_u2081_3068_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_u2082_3069_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_h_u2081_3070_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_h_u2082_3071_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3072_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3073_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3074_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3075_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3076_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3077_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3078_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3079_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3080_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3081_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_3082_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_3083_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_3082_);
    crate::leanh::lean_dec_ref(v_a_3081_);
    crate::leanh::lean_dec(v_a_3080_);
    crate::leanh::lean_dec_ref(v_a_3079_);
    crate::leanh::lean_dec(v_a_3078_);
    crate::leanh::lean_dec_ref(v_a_3077_);
    crate::leanh::lean_dec(v_a_3076_);
    crate::leanh::lean_dec_ref(v_a_3075_);
    crate::leanh::lean_dec(v_a_3074_);
    crate::leanh::lean_dec(v_a_3073_);
    crate::leanh::lean_dec(v_a_3072_);
    crate::leanh::lean_dec_ref(v_k_u2082_3069_);
    crate::leanh::lean_dec_ref(v_k_u2081_3068_);
    return v_res_3084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(
    mut v_p_u2081_3085_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3086_: *mut crate::leanh::LeanObject,
    mut v_v_3087_: *mut crate::leanh::LeanObject,
    mut v_a_3088_: *mut crate::leanh::LeanObject,
    mut v_a_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___y_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3109_: u8 = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3127_: u8 = 0;
    let mut v_k_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3129_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_nodes_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3158_: u8 = 0;
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3162_: u8 = 0;
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_w_3100_ = crate::leanh::lean_ctor_get(v_p_u2081_3085_, 0);
                v_k_3101_ = crate::leanh::lean_ctor_get(v_p_u2081_3085_, 1);
                v_proof_3102_ = crate::leanh::lean_ctor_get(v_p_u2081_3085_, 2);
                v_isSharedCheck_3163_ = (!crate::leanh::lean_is_exclusive(v_p_u2081_3085_)) as u8;
                if v_isSharedCheck_3163_ == 0 {
                    v___x_3104_ = v_p_u2081_3085_;
                    v_isShared_3105_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_3102_);
                    crate::leanh::lean_inc(v_k_3101_);
                    crate::leanh::lean_inc(v_w_3100_);
                    crate::leanh::lean_dec(v_p_u2081_3085_);
                    v___x_3104_ = crate::leanh::lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_w_3115_ = crate::leanh::lean_ctor_get(v_p_u2082_3086_, 0);
                crate::leanh::lean_inc(v_w_3115_);
                v_k_3116_ = crate::leanh::lean_ctor_get(v_p_u2082_3086_, 1);
                crate::leanh::lean_inc_ref(v_k_3116_);
                v_proof_3117_ = crate::leanh::lean_ctor_get(v_p_u2082_3086_, 2);
                crate::leanh::lean_inc_ref(v_proof_3117_);
                crate::leanh::lean_dec_ref(v_p_u2082_3086_);
                v___x_3118_ = l_Lean_Meta_Grind_Order_getStruct(
                    v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_,
                    v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_,
                );
                if crate::leanh::lean_obj_tag(v___x_3118_) == 0 {
                    v_a_3119_ = crate::leanh::lean_ctor_get(v___x_3118_, 0);
                    crate::leanh::lean_inc(v_a_3119_);
                    crate::leanh::lean_dec_ref_known(v___x_3118_, 1);
                    v_nodes_3139_ = crate::leanh::lean_ctor_get(v_a_3119_, 14);
                    crate::leanh::lean_inc_ref(v_nodes_3139_);
                    crate::leanh::lean_dec(v_a_3119_);
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
                    crate::leanh::lean_dec_ref(v_proof_3117_);
                    crate::leanh::lean_dec_ref(v_k_3116_);
                    crate::leanh::lean_dec(v_w_3115_);
                    crate::leanh::lean_del_object(v___x_3104_);
                    crate::leanh::lean_dec_ref(v_proof_3102_);
                    crate::leanh::lean_dec_ref(v_k_3101_);
                    crate::leanh::lean_dec(v_w_3100_);
                    v_a_3155_ = crate::leanh::lean_ctor_get(v___x_3118_, 0);
                    v_isSharedCheck_3162_ = (!crate::leanh::lean_is_exclusive(v___x_3118_)) as u8;
                    if v_isSharedCheck_3162_ == 0 {
                        v___x_3157_ = v___x_3118_;
                        v_isShared_3158_ = v_isSharedCheck_3162_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3155_);
                        crate::leanh::lean_dec(v___x_3118_);
                        v___x_3157_ = crate::leanh::lean_box(0);
                        v_isShared_3158_ = v_isSharedCheck_3162_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3110_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3110_, 0, v___y_3107_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3110_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_3109_,
                );
                if v_isShared_3105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3104_, 2, v___y_3108_);
                    crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3110_);
                    v___x_3112_ = v___x_3104_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_w_3100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 2, v___y_3108_);
                    v___x_3112_ = v_reuseFailAlloc_3114_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3113_, 0, v___x_3112_);
                return v___x_3113_;
            }
            4 => {
                v___x_3124_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v___y_3121_, v___y_3122_, v___y_3123_, v_k_3101_, v_k_3116_, v_proof_3102_, v_proof_3117_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
                if crate::leanh::lean_obj_tag(v___x_3124_) == 0 {
                    v_a_3125_ = crate::leanh::lean_ctor_get(v___x_3124_, 0);
                    crate::leanh::lean_inc(v_a_3125_);
                    crate::leanh::lean_dec_ref_known(v___x_3124_, 1);
                    v_k_3126_ = crate::leanh::lean_ctor_get(v_k_3101_, 0);
                    crate::leanh::lean_inc(v_k_3126_);
                    v_strict_3127_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3101_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_k_3101_);
                    v_k_3128_ = crate::leanh::lean_ctor_get(v_k_3116_, 0);
                    crate::leanh::lean_inc(v_k_3128_);
                    v_strict_3129_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3116_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_k_3116_);
                    v___x_3130_ = lean_int_add(v_k_3126_, v_k_3128_);
                    crate::leanh::lean_dec(v_k_3128_);
                    crate::leanh::lean_dec(v_k_3126_);
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
                    crate::leanh::lean_dec_ref(v_k_3116_);
                    crate::leanh::lean_del_object(v___x_3104_);
                    crate::leanh::lean_dec_ref(v_k_3101_);
                    crate::leanh::lean_dec(v_w_3100_);
                    v_a_3131_ = crate::leanh::lean_ctor_get(v___x_3124_, 0);
                    v_isSharedCheck_3138_ = (!crate::leanh::lean_is_exclusive(v___x_3124_)) as u8;
                    if v_isSharedCheck_3138_ == 0 {
                        v___x_3133_ = v___x_3124_;
                        v_isShared_3134_ = v_isSharedCheck_3138_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3131_);
                        crate::leanh::lean_dec(v___x_3124_);
                        v___x_3133_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
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
                    crate::leanh::lean_dec_ref(v_nodes_3139_);
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
                    crate::leanh::lean_dec_ref(v_nodes_3139_);
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
                    crate::leanh::lean_dec(v_w_3115_);
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
                    crate::leanh::lean_dec(v_w_3115_);
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
                    v_reuseFailAlloc_3161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
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
    mut v_p_u2081_3164_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3165_: *mut crate::leanh::LeanObject,
    mut v_v_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_3177_);
    crate::leanh::lean_dec_ref(v_a_3176_);
    crate::leanh::lean_dec(v_a_3175_);
    crate::leanh::lean_dec_ref(v_a_3174_);
    crate::leanh::lean_dec(v_a_3173_);
    crate::leanh::lean_dec_ref(v_a_3172_);
    crate::leanh::lean_dec(v_a_3171_);
    crate::leanh::lean_dec_ref(v_a_3170_);
    crate::leanh::lean_dec(v_a_3169_);
    crate::leanh::lean_dec(v_a_3168_);
    crate::leanh::lean_dec(v_a_3167_);
    crate::leanh::lean_dec(v_v_3166_);
    return v_res_3179_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkTrans(
    mut v_p_u2081_3180_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3181_: *mut crate::leanh::LeanObject,
    mut v_v_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
    mut v_a_3187_: *mut crate::leanh::LeanObject,
    mut v_a_3188_: *mut crate::leanh::LeanObject,
    mut v_a_3189_: *mut crate::leanh::LeanObject,
    mut v_a_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_a_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3195_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_,
                    v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_,
                );
                if crate::leanh::lean_obj_tag(v___x_3195_) == 0 {
                    v_a_3196_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                    crate::leanh::lean_inc(v_a_3196_);
                    crate::leanh::lean_dec_ref_known(v___x_3195_, 1);
                    v___x_3197_ = (crate::leanh::lean_unbox(v_a_3196_) as u8);
                    crate::leanh::lean_dec(v_a_3196_);
                    if v___x_3197_ == 0 {
                        v___x_3198_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore(v_p_u2081_3180_, v_p_u2082_3181_, v_v_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
                        return v___x_3198_;
                    } else {
                        v___x_3199_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffset(v_p_u2081_3180_, v_p_u2082_3181_, v_v_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
                        return v___x_3199_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_u2082_3181_);
                    crate::leanh::lean_dec_ref(v_p_u2081_3180_);
                    v_a_3200_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                    v_isSharedCheck_3207_ = (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                    if v_isSharedCheck_3207_ == 0 {
                        v___x_3202_ = v___x_3195_;
                        v_isShared_3203_ = v_isSharedCheck_3207_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3200_);
                        crate::leanh::lean_dec(v___x_3195_);
                        v___x_3202_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
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
    mut v_p_u2081_3208_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_3209_: *mut crate::leanh::LeanObject,
    mut v_v_3210_: *mut crate::leanh::LeanObject,
    mut v_a_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_3221_);
    crate::leanh::lean_dec_ref(v_a_3220_);
    crate::leanh::lean_dec(v_a_3219_);
    crate::leanh::lean_dec_ref(v_a_3218_);
    crate::leanh::lean_dec(v_a_3217_);
    crate::leanh::lean_dec_ref(v_a_3216_);
    crate::leanh::lean_dec(v_a_3215_);
    crate::leanh::lean_dec_ref(v_a_3214_);
    crate::leanh::lean_dec(v_a_3213_);
    crate::leanh::lean_dec(v_a_3212_);
    crate::leanh::lean_dec(v_a_3211_);
    crate::leanh::lean_dec(v_v_3210_);
    return v_res_3223_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3224_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_3224_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(
    mut v_msg_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910__overap_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3238_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___closed__0);
    v___f_3239_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3239_, 0, v___x_3238_);
    v___x_1910__overap_3240_ = lean_panic_fn_borrowed(v___f_3239_, v_msg_3225_);
    crate::leanh::lean_dec_ref(v___f_3239_);
    crate::leanh::lean_inc(v___y_3236_);
    crate::leanh::lean_inc_ref(v___y_3235_);
    crate::leanh::lean_inc(v___y_3234_);
    crate::leanh::lean_inc_ref(v___y_3233_);
    crate::leanh::lean_inc(v___y_3232_);
    crate::leanh::lean_inc_ref(v___y_3231_);
    crate::leanh::lean_inc(v___y_3230_);
    crate::leanh::lean_inc_ref(v___y_3229_);
    crate::leanh::lean_inc(v___y_3228_);
    crate::leanh::lean_inc(v___y_3227_);
    crate::leanh::lean_inc(v___y_3226_);
    v___x_3241_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_3241_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0___boxed(
    mut v_msg_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3255_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v_msg_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
    crate::leanh::lean_dec(v___y_3253_);
    crate::leanh::lean_dec_ref(v___y_3252_);
    crate::leanh::lean_dec(v___y_3251_);
    crate::leanh::lean_dec_ref(v___y_3250_);
    crate::leanh::lean_dec(v___y_3249_);
    crate::leanh::lean_dec_ref(v___y_3248_);
    crate::leanh::lean_dec(v___y_3247_);
    crate::leanh::lean_dec_ref(v___y_3246_);
    crate::leanh::lean_dec(v___y_3245_);
    crate::leanh::lean_dec(v___y_3244_);
    crate::leanh::lean_dec(v___y_3243_);
    return v_res_3255_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__2;
    v___x_3260_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3261_ = crate::leanh::lean_unsigned_to_nat(133);
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
    mut v_u_3271_: *mut crate::leanh::LeanObject,
    mut v_v_3272_: *mut crate::leanh::LeanObject,
    mut v_k_3273_: *mut crate::leanh::LeanObject,
    mut v_huv_3274_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
    mut v_a_3279_: *mut crate::leanh::LeanObject,
    mut v_a_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3291_: u8 = 0;
    let mut v_strict_3292_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_3291_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_3273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_strict_3292_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_x27_3275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_3291_ == 0 {
                    if v_strict_3292_ == 0 {
                        crate::leanh::lean_dec_ref(v_v_3272_);
                        crate::leanh::lean_dec_ref(v_u_3271_);
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
                        crate::leanh::lean_dec_ref(v_v_3272_);
                        crate::leanh::lean_dec_ref(v_u_3271_);
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
                v___x_3289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__3);
                v___x_3290_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_3289_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
                return v___x_3290_;
            }
            2 => {
                if v_strict_3291_ == 0 {
                    crate::leanh::lean_dec_ref(v_huv_3274_);
                    crate::leanh::lean_dec_ref(v_v_3272_);
                    crate::leanh::lean_dec_ref(v_u_3271_);
                    state = 1;
                    continue;
                } else {
                    if v_strict_3292_ == 0 {
                        v___x_3294_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore___closed__5;
                        v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_3294_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
                        if crate::leanh::lean_obj_tag(v___x_3295_) == 0 {
                            v_a_3296_ = crate::leanh::lean_ctor_get(v___x_3295_, 0);
                            v_isSharedCheck_3304_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3295_)) as u8;
                            if v_isSharedCheck_3304_ == 0 {
                                v___x_3298_ = v___x_3295_;
                                v_isShared_3299_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3296_);
                                crate::leanh::lean_dec(v___x_3295_);
                                v___x_3298_ = crate::leanh::lean_box(0);
                                v_isShared_3299_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_huv_3274_);
                            crate::leanh::lean_dec_ref(v_v_3272_);
                            crate::leanh::lean_dec_ref(v_u_3271_);
                            return v___x_3295_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_huv_3274_);
                        crate::leanh::lean_dec_ref(v_v_3272_);
                        crate::leanh::lean_dec_ref(v_u_3271_);
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3300_ = l_Lean_mkApp3(v_a_3296_, v_u_3271_, v_v_3272_, v_huv_3274_);
                if v_isShared_3299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3298_, 0, v___x_3300_);
                    v___x_3302_ = v___x_3298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3307_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3308_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3309_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3310_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3311_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3312_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3313_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3314_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3315_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3316_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3317_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3318_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3319_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3320_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3321_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3322_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3323_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_3307_, v_v_3308_, v_k_3309_, v_huv_3310_, v_k_x27_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
    crate::leanh::lean_dec(v_a_3322_);
    crate::leanh::lean_dec_ref(v_a_3321_);
    crate::leanh::lean_dec(v_a_3320_);
    crate::leanh::lean_dec_ref(v_a_3319_);
    crate::leanh::lean_dec(v_a_3318_);
    crate::leanh::lean_dec_ref(v_a_3317_);
    crate::leanh::lean_dec(v_a_3316_);
    crate::leanh::lean_dec_ref(v_a_3315_);
    crate::leanh::lean_dec(v_a_3314_);
    crate::leanh::lean_dec(v_a_3313_);
    crate::leanh::lean_dec(v_a_3312_);
    crate::leanh::lean_dec_ref(v_k_x27_3311_);
    crate::leanh::lean_dec_ref(v_k_3309_);
    return v_res_3324_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(
    mut v_u_3349_: *mut crate::leanh::LeanObject,
    mut v_v_3350_: *mut crate::leanh::LeanObject,
    mut v_k_3351_: *mut crate::leanh::LeanObject,
    mut v_huv_3352_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3374_: u8 = 0;
    let mut v___y_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3405_: u8 = 0;
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3408_: u8 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3373_ = crate::leanh::lean_ctor_get(v_k_x27_3353_, 0);
                v_strict_3374_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_x27_3353_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_3374_ == 0 {
                    v_strict_3405_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_strict_3408_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_3372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3372_, 0, v___x_3371_);
                return v___x_3372_;
            }
            2 => {
                v___x_3378_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3379_ = lean_int_dec_le(v___x_3378_, v_k_3373_);
                if v___x_3379_ == 0 {
                    v___x_3380_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3381_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3383_ = lean_int_neg(v_k_3373_);
                    v___x_3384_ = l_Int_toNat(v___x_3383_);
                    crate::leanh::lean_dec(v___x_3383_);
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
                crate::leanh::lean_inc(v___y_3390_);
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
                if crate::leanh::lean_obj_tag(v___x_3391_) == 0 {
                    v_a_3392_ = crate::leanh::lean_ctor_get(v___x_3391_, 0);
                    crate::leanh::lean_inc(v_a_3392_);
                    crate::leanh::lean_dec_ref_known(v___x_3391_, 1);
                    v_k_3393_ = crate::leanh::lean_ctor_get(v_k_3351_, 0);
                    v___x_3394_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3395_ = lean_int_dec_le(v___x_3394_, v_k_3393_);
                    if v___x_3395_ == 0 {
                        v___x_3396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3397_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3398_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3399_ = lean_int_neg(v_k_3393_);
                        v___x_3400_ = l_Int_toNat(v___x_3399_);
                        crate::leanh::lean_dec(v___x_3399_);
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
                    crate::leanh::lean_dec_ref(v_huv_3352_);
                    crate::leanh::lean_dec_ref(v_v_3350_);
                    crate::leanh::lean_dec_ref(v_u_3349_);
                    return v___x_3391_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3411_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3412_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3413_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3414_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3415_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3416_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3417_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3418_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3419_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3420_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3421_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3422_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3423_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3424_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3425_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3426_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3427_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_3411_, v_v_3412_, v_k_3413_, v_huv_3414_, v_k_x27_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
    crate::leanh::lean_dec(v_a_3426_);
    crate::leanh::lean_dec_ref(v_a_3425_);
    crate::leanh::lean_dec(v_a_3424_);
    crate::leanh::lean_dec_ref(v_a_3423_);
    crate::leanh::lean_dec(v_a_3422_);
    crate::leanh::lean_dec_ref(v_a_3421_);
    crate::leanh::lean_dec(v_a_3420_);
    crate::leanh::lean_dec_ref(v_a_3419_);
    crate::leanh::lean_dec(v_a_3418_);
    crate::leanh::lean_dec(v_a_3417_);
    crate::leanh::lean_dec(v_a_3416_);
    crate::leanh::lean_dec_ref(v_k_x27_3415_);
    crate::leanh::lean_dec_ref(v_k_3413_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(
    mut v_u_3429_: *mut crate::leanh::LeanObject,
    mut v_v_3430_: *mut crate::leanh::LeanObject,
    mut v_k_3431_: *mut crate::leanh::LeanObject,
    mut v_huv_3432_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3446_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_,
                    v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_,
                );
                if crate::leanh::lean_obj_tag(v___x_3446_) == 0 {
                    v_a_3447_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                    crate::leanh::lean_inc(v_a_3447_);
                    crate::leanh::lean_dec_ref_known(v___x_3446_, 1);
                    v___x_3448_ = (crate::leanh::lean_unbox(v_a_3447_) as u8);
                    crate::leanh::lean_dec(v_a_3447_);
                    if v___x_3448_ == 0 {
                        v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore(v_u_3429_, v_v_3430_, v_k_3431_, v_huv_3432_, v_k_x27_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3449_;
                    } else {
                        v___x_3450_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofOffset(v_u_3429_, v_v_3430_, v_k_3431_, v_huv_3432_, v_k_x27_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3450_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_huv_3432_);
                    crate::leanh::lean_dec_ref(v_v_3430_);
                    crate::leanh::lean_dec_ref(v_u_3429_);
                    v_a_3451_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                    v_isSharedCheck_3458_ = (!crate::leanh::lean_is_exclusive(v___x_3446_)) as u8;
                    if v_isSharedCheck_3458_ == 0 {
                        v___x_3453_ = v___x_3446_;
                        v_isShared_3454_ = v_isSharedCheck_3458_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3451_);
                        crate::leanh::lean_dec(v___x_3446_);
                        v___x_3453_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3459_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3460_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3461_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3462_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3463_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3464_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3465_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3466_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3467_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3468_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3469_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3470_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3471_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3472_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3473_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3474_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3475_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_3474_);
    crate::leanh::lean_dec_ref(v_a_3473_);
    crate::leanh::lean_dec(v_a_3472_);
    crate::leanh::lean_dec_ref(v_a_3471_);
    crate::leanh::lean_dec(v_a_3470_);
    crate::leanh::lean_dec_ref(v_a_3469_);
    crate::leanh::lean_dec(v_a_3468_);
    crate::leanh::lean_dec_ref(v_a_3467_);
    crate::leanh::lean_dec(v_a_3466_);
    crate::leanh::lean_dec(v_a_3465_);
    crate::leanh::lean_dec(v_a_3464_);
    crate::leanh::lean_dec_ref(v_k_x27_3463_);
    crate::leanh::lean_dec_ref(v_k_3461_);
    return v_res_3476_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(
    mut v_u_3489_: *mut crate::leanh::LeanObject,
    mut v_k_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3510_: u8 = 0;
    let mut v___y_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3509_ = crate::leanh::lean_ctor_get(v_k_3490_, 0);
                v_strict_3510_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_3490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_3508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3507_);
                return v___x_3508_;
            }
            2 => {
                crate::leanh::lean_inc(v___y_3512_);
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
                if crate::leanh::lean_obj_tag(v___x_3513_) == 0 {
                    v_a_3514_ = crate::leanh::lean_ctor_get(v___x_3513_, 0);
                    crate::leanh::lean_inc(v_a_3514_);
                    crate::leanh::lean_dec_ref_known(v___x_3513_, 1);
                    v___x_3515_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3516_ = lean_int_dec_le(v___x_3515_, v_k_3509_);
                    if v___x_3516_ == 0 {
                        v___x_3517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3520_ = lean_int_neg(v_k_3509_);
                        v___x_3521_ = l_Int_toNat(v___x_3520_);
                        crate::leanh::lean_dec(v___x_3520_);
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
                    crate::leanh::lean_dec_ref(v_u_3489_);
                    return v___x_3513_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset___boxed(
    mut v_u_3528_: *mut crate::leanh::LeanObject,
    mut v_k_3529_: *mut crate::leanh::LeanObject,
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_a_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
    mut v_a_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
    mut v_a_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_3528_, v_k_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
    crate::leanh::lean_dec(v_a_3540_);
    crate::leanh::lean_dec_ref(v_a_3539_);
    crate::leanh::lean_dec(v_a_3538_);
    crate::leanh::lean_dec_ref(v_a_3537_);
    crate::leanh::lean_dec(v_a_3536_);
    crate::leanh::lean_dec_ref(v_a_3535_);
    crate::leanh::lean_dec(v_a_3534_);
    crate::leanh::lean_dec_ref(v_a_3533_);
    crate::leanh::lean_dec(v_a_3532_);
    crate::leanh::lean_dec(v_a_3531_);
    crate::leanh::lean_dec(v_a_3530_);
    crate::leanh::lean_dec_ref(v_k_3529_);
    return v_res_3542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(
    mut v_u_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_3563_) == 0 {
                    v_a_3564_ = crate::leanh::lean_ctor_get(v___x_3563_, 0);
                    v_isSharedCheck_3572_ = (!crate::leanh::lean_is_exclusive(v___x_3563_)) as u8;
                    if v_isSharedCheck_3572_ == 0 {
                        v___x_3566_ = v___x_3563_;
                        v_isShared_3567_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3564_);
                        crate::leanh::lean_dec(v___x_3563_);
                        v___x_3566_ = crate::leanh::lean_box(0);
                        v_isShared_3567_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_u_3549_);
                    return v___x_3563_;
                }
            }
            1 => {
                v___x_3568_ = l_Lean_Expr_app___override(v_a_3564_, v_u_3549_);
                if v_isShared_3567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3566_, 0, v___x_3568_);
                    v___x_3570_ = v___x_3566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
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
    mut v_u_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
    mut v_a_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
    crate::leanh::lean_dec(v_a_3584_);
    crate::leanh::lean_dec_ref(v_a_3583_);
    crate::leanh::lean_dec(v_a_3582_);
    crate::leanh::lean_dec_ref(v_a_3581_);
    crate::leanh::lean_dec(v_a_3580_);
    crate::leanh::lean_dec_ref(v_a_3579_);
    crate::leanh::lean_dec(v_a_3578_);
    crate::leanh::lean_dec_ref(v_a_3577_);
    crate::leanh::lean_dec(v_a_3576_);
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec(v_a_3574_);
    return v_res_3586_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__1;
    v___x_3590_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3591_ = crate::leanh::lean_unsigned_to_nat(175);
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
    mut v_u_3595_: *mut crate::leanh::LeanObject,
    mut v_k_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
    mut v_a_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v_strict_3612_: u8 = 0;
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3609_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_,
                    v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_,
                );
                if crate::leanh::lean_obj_tag(v___x_3609_) == 0 {
                    v_a_3610_ = crate::leanh::lean_ctor_get(v___x_3609_, 0);
                    crate::leanh::lean_inc(v_a_3610_);
                    crate::leanh::lean_dec_ref_known(v___x_3609_, 1);
                    v___x_3611_ = (crate::leanh::lean_unbox(v_a_3610_) as u8);
                    crate::leanh::lean_dec(v_a_3610_);
                    if v___x_3611_ == 0 {
                        v_strict_3612_ = crate::leanh::lean_ctor_get_uint8(
                            v_k_3596_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_strict_3612_ == 0 {
                            v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofCore(v_u_3595_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                            return v___x_3613_;
                        } else {
                            crate::leanh::lean_dec_ref(v_u_3595_);
                            v___x_3614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2_once), _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof___closed__2);
                            v___x_3615_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqTrueProofCore_spec__0(v___x_3614_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                            return v___x_3615_;
                        }
                    } else {
                        v___x_3616_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProofOffset(v_u_3595_, v_k_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
                        return v___x_3616_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_u_3595_);
                    v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3624_ = (!crate::leanh::lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3619_ = v___x_3609_;
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3617_);
                        crate::leanh::lean_dec(v___x_3609_);
                        v___x_3619_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
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
    mut v_u_3625_: *mut crate::leanh::LeanObject,
    mut v_k_3626_: *mut crate::leanh::LeanObject,
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
    mut v_a_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(
        v_u_3625_, v_k_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_,
        v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_,
    );
    crate::leanh::lean_dec(v_a_3637_);
    crate::leanh::lean_dec_ref(v_a_3636_);
    crate::leanh::lean_dec(v_a_3635_);
    crate::leanh::lean_dec_ref(v_a_3634_);
    crate::leanh::lean_dec(v_a_3633_);
    crate::leanh::lean_dec_ref(v_a_3632_);
    crate::leanh::lean_dec(v_a_3631_);
    crate::leanh::lean_dec_ref(v_a_3630_);
    crate::leanh::lean_dec(v_a_3629_);
    crate::leanh::lean_dec(v_a_3628_);
    crate::leanh::lean_dec(v_a_3627_);
    crate::leanh::lean_dec_ref(v_k_3626_);
    return v_res_3639_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(
    mut v_msg_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3641_ = crate::leanh::lean_box(0);
    v___x_3642_ = lean_panic_fn_borrowed(v___x_3641_, v_msg_3640_);
    return v___x_3642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3645_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__1;
    v___x_3646_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3647_ = crate::leanh::lean_unsigned_to_nat(183);
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
    mut v_u_3669_: *mut crate::leanh::LeanObject,
    mut v_v_3670_: *mut crate::leanh::LeanObject,
    mut v_k_3671_: *mut crate::leanh::LeanObject,
    mut v_huv_3672_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3673_: *mut crate::leanh::LeanObject,
    mut v_a_3674_: *mut crate::leanh::LeanObject,
    mut v_a_3675_: *mut crate::leanh::LeanObject,
    mut v_a_3676_: *mut crate::leanh::LeanObject,
    mut v_a_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v_a_3679_: *mut crate::leanh::LeanObject,
    mut v_a_3680_: *mut crate::leanh::LeanObject,
    mut v_a_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3697_: u8 = 0;
    let mut v_strict_3698_: u8 = 0;
    let mut v_strict_3699_: u8 = 0;
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3703_: u8 = 0;
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_3698_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_x27_3673_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_3698_ == 0 {
                    v_strict_3699_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3671_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_strict_3699_ == 0 {
                        v___x_3700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore___closed__2);
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
                    v_strict_3703_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3671_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                if crate::leanh::lean_obj_tag(v___x_3688_) == 0 {
                    v_a_3689_ = crate::leanh::lean_ctor_get(v___x_3688_, 0);
                    v_isSharedCheck_3697_ = (!crate::leanh::lean_is_exclusive(v___x_3688_)) as u8;
                    if v_isSharedCheck_3697_ == 0 {
                        v___x_3691_ = v___x_3688_;
                        v_isShared_3692_ = v_isSharedCheck_3697_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3689_);
                        crate::leanh::lean_dec(v___x_3688_);
                        v___x_3691_ = crate::leanh::lean_box(0);
                        v_isShared_3692_ = v_isSharedCheck_3697_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_huv_3672_);
                    crate::leanh::lean_dec_ref(v_v_3670_);
                    crate::leanh::lean_dec_ref(v_u_3669_);
                    return v___x_3688_;
                }
            }
            2 => {
                v___x_3693_ = l_Lean_mkApp3(v_a_3689_, v_u_3669_, v_v_3670_, v_huv_3672_);
                if v_isShared_3692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3693_);
                    v___x_3695_ = v___x_3691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3706_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3707_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3708_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3709_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3710_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3711_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3712_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3713_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3714_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3715_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3716_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3717_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3718_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3719_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3720_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3721_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3722_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3723_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_3706_, v_v_3707_, v_k_3708_, v_huv_3709_, v_k_x27_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
    crate::leanh::lean_dec(v_a_3721_);
    crate::leanh::lean_dec_ref(v_a_3720_);
    crate::leanh::lean_dec(v_a_3719_);
    crate::leanh::lean_dec_ref(v_a_3718_);
    crate::leanh::lean_dec(v_a_3717_);
    crate::leanh::lean_dec_ref(v_a_3716_);
    crate::leanh::lean_dec(v_a_3715_);
    crate::leanh::lean_dec_ref(v_a_3714_);
    crate::leanh::lean_dec(v_a_3713_);
    crate::leanh::lean_dec(v_a_3712_);
    crate::leanh::lean_dec(v_a_3711_);
    crate::leanh::lean_dec_ref(v_k_x27_3710_);
    crate::leanh::lean_dec_ref(v_k_3708_);
    return v_res_3723_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(
    mut v_u_3748_: *mut crate::leanh::LeanObject,
    mut v_v_3749_: *mut crate::leanh::LeanObject,
    mut v_k_3750_: *mut crate::leanh::LeanObject,
    mut v_huv_3751_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3773_: u8 = 0;
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: u8 = 0;
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3804_: u8 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3807_: u8 = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3772_ = crate::leanh::lean_ctor_get(v_k_x27_3752_, 0);
                v_strict_3773_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_x27_3752_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_3773_ == 0 {
                    v_strict_3804_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_strict_3807_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_3750_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_3771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3771_, 0, v___x_3770_);
                return v___x_3771_;
            }
            2 => {
                v___x_3777_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                v___x_3778_ = lean_int_dec_le(v___x_3777_, v_k_3772_);
                if v___x_3778_ == 0 {
                    v___x_3779_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                    v___x_3780_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                    v___x_3781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                    v___x_3782_ = lean_int_neg(v_k_3772_);
                    v___x_3783_ = l_Int_toNat(v___x_3782_);
                    crate::leanh::lean_dec(v___x_3782_);
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
                crate::leanh::lean_inc(v___y_3789_);
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
                if crate::leanh::lean_obj_tag(v___x_3790_) == 0 {
                    v_a_3791_ = crate::leanh::lean_ctor_get(v___x_3790_, 0);
                    crate::leanh::lean_inc(v_a_3791_);
                    crate::leanh::lean_dec_ref_known(v___x_3790_, 1);
                    v_k_3792_ = crate::leanh::lean_ctor_get(v_k_3750_, 0);
                    v___x_3793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3794_ = lean_int_dec_le(v___x_3793_, v_k_3792_);
                    if v___x_3794_ == 0 {
                        v___x_3795_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3797_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3798_ = lean_int_neg(v_k_3792_);
                        v___x_3799_ = l_Int_toNat(v___x_3798_);
                        crate::leanh::lean_dec(v___x_3798_);
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
                    crate::leanh::lean_dec_ref(v_huv_3751_);
                    crate::leanh::lean_dec_ref(v_v_3749_);
                    crate::leanh::lean_dec_ref(v_u_3748_);
                    return v___x_3790_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3810_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3811_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3812_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3813_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3814_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3815_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3816_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3817_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3818_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3819_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3820_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3821_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3822_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3823_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3824_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3825_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3826_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_3810_, v_v_3811_, v_k_3812_, v_huv_3813_, v_k_x27_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
    crate::leanh::lean_dec(v_a_3825_);
    crate::leanh::lean_dec_ref(v_a_3824_);
    crate::leanh::lean_dec(v_a_3823_);
    crate::leanh::lean_dec_ref(v_a_3822_);
    crate::leanh::lean_dec(v_a_3821_);
    crate::leanh::lean_dec_ref(v_a_3820_);
    crate::leanh::lean_dec(v_a_3819_);
    crate::leanh::lean_dec_ref(v_a_3818_);
    crate::leanh::lean_dec(v_a_3817_);
    crate::leanh::lean_dec(v_a_3816_);
    crate::leanh::lean_dec(v_a_3815_);
    crate::leanh::lean_dec_ref(v_k_x27_3814_);
    crate::leanh::lean_dec_ref(v_k_3812_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(
    mut v_u_3828_: *mut crate::leanh::LeanObject,
    mut v_v_3829_: *mut crate::leanh::LeanObject,
    mut v_k_3830_: *mut crate::leanh::LeanObject,
    mut v_huv_3831_: *mut crate::leanh::LeanObject,
    mut v_k_x27_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_a_3835_: *mut crate::leanh::LeanObject,
    mut v_a_3836_: *mut crate::leanh::LeanObject,
    mut v_a_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
    mut v_a_3839_: *mut crate::leanh::LeanObject,
    mut v_a_3840_: *mut crate::leanh::LeanObject,
    mut v_a_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3845_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_,
                    v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_,
                );
                if crate::leanh::lean_obj_tag(v___x_3845_) == 0 {
                    v_a_3846_ = crate::leanh::lean_ctor_get(v___x_3845_, 0);
                    crate::leanh::lean_inc(v_a_3846_);
                    crate::leanh::lean_dec_ref_known(v___x_3845_, 1);
                    v___x_3847_ = (crate::leanh::lean_unbox(v_a_3846_) as u8);
                    crate::leanh::lean_dec(v_a_3846_);
                    if v___x_3847_ == 0 {
                        v___x_3848_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore(v_u_3828_, v_v_3829_, v_k_3830_, v_huv_3831_, v_k_x27_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
                        return v___x_3848_;
                    } else {
                        v___x_3849_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofOffset(v_u_3828_, v_v_3829_, v_k_3830_, v_huv_3831_, v_k_x27_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
                        return v___x_3849_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_huv_3831_);
                    crate::leanh::lean_dec_ref(v_v_3829_);
                    crate::leanh::lean_dec_ref(v_u_3828_);
                    v_a_3850_ = crate::leanh::lean_ctor_get(v___x_3845_, 0);
                    v_isSharedCheck_3857_ = (!crate::leanh::lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3857_ == 0 {
                        v___x_3852_ = v___x_3845_;
                        v_isShared_3853_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3850_);
                        crate::leanh::lean_dec(v___x_3845_);
                        v___x_3852_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3858_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_3859_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3860_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_huv_3861_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_x27_3862_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_3863_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_3864_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3865_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_3866_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_3867_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3868_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3869_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_3870_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_3871_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_3872_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3873_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3874_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_3873_);
    crate::leanh::lean_dec_ref(v_a_3872_);
    crate::leanh::lean_dec(v_a_3871_);
    crate::leanh::lean_dec_ref(v_a_3870_);
    crate::leanh::lean_dec(v_a_3869_);
    crate::leanh::lean_dec_ref(v_a_3868_);
    crate::leanh::lean_dec(v_a_3867_);
    crate::leanh::lean_dec_ref(v_a_3866_);
    crate::leanh::lean_dec(v_a_3865_);
    crate::leanh::lean_dec(v_a_3864_);
    crate::leanh::lean_dec(v_a_3863_);
    crate::leanh::lean_dec_ref(v_k_x27_3862_);
    crate::leanh::lean_dec_ref(v_k_3860_);
    return v_res_3875_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(
    mut v_u_3888_: *mut crate::leanh::LeanObject,
    mut v_k_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
    mut v_a_3898_: *mut crate::leanh::LeanObject,
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v_a_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_3909_: u8 = 0;
    let mut v___y_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_3908_ = crate::leanh::lean_ctor_get(v_k_3889_, 0);
                v_strict_3909_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_3889_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_3907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3907_, 0, v___x_3906_);
                return v___x_3907_;
            }
            2 => {
                crate::leanh::lean_inc(v___y_3911_);
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
                if crate::leanh::lean_obj_tag(v___x_3912_) == 0 {
                    v_a_3913_ = crate::leanh::lean_ctor_get(v___x_3912_, 0);
                    crate::leanh::lean_inc(v_a_3913_);
                    crate::leanh::lean_dec_ref_known(v___x_3912_, 1);
                    v___x_3914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_3915_ = lean_int_dec_le(v___x_3914_, v_k_3908_);
                    if v___x_3915_ == 0 {
                        v___x_3916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_3917_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_3918_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_3919_ = lean_int_neg(v_k_3908_);
                        v___x_3920_ = l_Int_toNat(v___x_3919_);
                        crate::leanh::lean_dec(v___x_3919_);
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
                    crate::leanh::lean_dec_ref(v_u_3888_);
                    return v___x_3912_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset___boxed(
    mut v_u_3927_: *mut crate::leanh::LeanObject,
    mut v_k_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v_a_3930_: *mut crate::leanh::LeanObject,
    mut v_a_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3941_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofOffset(v_u_3927_, v_k_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
    crate::leanh::lean_dec(v_a_3939_);
    crate::leanh::lean_dec_ref(v_a_3938_);
    crate::leanh::lean_dec(v_a_3937_);
    crate::leanh::lean_dec_ref(v_a_3936_);
    crate::leanh::lean_dec(v_a_3935_);
    crate::leanh::lean_dec_ref(v_a_3934_);
    crate::leanh::lean_dec(v_a_3933_);
    crate::leanh::lean_dec_ref(v_a_3932_);
    crate::leanh::lean_dec(v_a_3931_);
    crate::leanh::lean_dec(v_a_3930_);
    crate::leanh::lean_dec(v_a_3929_);
    crate::leanh::lean_dec_ref(v_k_3928_);
    return v_res_3941_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(
    mut v_u_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3961_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore___closed__1;
                v___x_3962_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPrefix(v___x_3961_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
                if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
                    v_a_3963_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
                    v_isSharedCheck_3971_ = (!crate::leanh::lean_is_exclusive(v___x_3962_)) as u8;
                    if v_isSharedCheck_3971_ == 0 {
                        v___x_3965_ = v___x_3962_;
                        v_isShared_3966_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3963_);
                        crate::leanh::lean_dec(v___x_3962_);
                        v___x_3965_ = crate::leanh::lean_box(0);
                        v_isShared_3966_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_u_3948_);
                    return v___x_3962_;
                }
            }
            1 => {
                v___x_3967_ = l_Lean_Expr_app___override(v_a_3963_, v_u_3948_);
                if v_isShared_3966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3967_);
                    v___x_3969_ = v___x_3965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
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
    mut v_u_3972_: *mut crate::leanh::LeanObject,
    mut v_a_3973_: *mut crate::leanh::LeanObject,
    mut v_a_3974_: *mut crate::leanh::LeanObject,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
    mut v_a_3977_: *mut crate::leanh::LeanObject,
    mut v_a_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v_a_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
    mut v_a_3983_: *mut crate::leanh::LeanObject,
    mut v_a_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProofCore(v_u_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
    crate::leanh::lean_dec(v_a_3983_);
    crate::leanh::lean_dec_ref(v_a_3982_);
    crate::leanh::lean_dec(v_a_3981_);
    crate::leanh::lean_dec_ref(v_a_3980_);
    crate::leanh::lean_dec(v_a_3979_);
    crate::leanh::lean_dec_ref(v_a_3978_);
    crate::leanh::lean_dec(v_a_3977_);
    crate::leanh::lean_dec_ref(v_a_3976_);
    crate::leanh::lean_dec(v_a_3975_);
    crate::leanh::lean_dec(v_a_3974_);
    crate::leanh::lean_dec(v_a_3973_);
    return v_res_3985_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__1;
    v___x_3989_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3990_ = crate::leanh::lean_unsigned_to_nat(228);
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
    mut v_u_3994_: *mut crate::leanh::LeanObject,
    mut v_k_3995_: *mut crate::leanh::LeanObject,
    mut v_a_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v_strict_4011_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4008_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_,
                    v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_,
                );
                if crate::leanh::lean_obj_tag(v___x_4008_) == 0 {
                    v_a_4009_ = crate::leanh::lean_ctor_get(v___x_4008_, 0);
                    crate::leanh::lean_inc(v_a_4009_);
                    crate::leanh::lean_dec_ref_known(v___x_4008_, 1);
                    v___x_4010_ = (crate::leanh::lean_unbox(v_a_4009_) as u8);
                    crate::leanh::lean_dec(v_a_4009_);
                    if v___x_4010_ == 0 {
                        v_strict_4011_ = crate::leanh::lean_ctor_get_uint8(
                            v_k_3995_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_strict_4011_ == 0 {
                            crate::leanh::lean_dec_ref(v_u_3994_);
                            v___x_4012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2_once), _init_l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof___closed__2);
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
                    crate::leanh::lean_dec_ref(v_u_3994_);
                    v_a_4016_ = crate::leanh::lean_ctor_get(v___x_4008_, 0);
                    v_isSharedCheck_4023_ = (!crate::leanh::lean_is_exclusive(v___x_4008_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4018_ = v___x_4008_;
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4016_);
                        crate::leanh::lean_dec(v___x_4008_);
                        v___x_4018_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
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
    mut v_u_4024_: *mut crate::leanh::LeanObject,
    mut v_k_4025_: *mut crate::leanh::LeanObject,
    mut v_a_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
    mut v_a_4028_: *mut crate::leanh::LeanObject,
    mut v_a_4029_: *mut crate::leanh::LeanObject,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4038_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(
        v_u_4024_, v_k_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_,
        v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_,
    );
    crate::leanh::lean_dec(v_a_4036_);
    crate::leanh::lean_dec_ref(v_a_4035_);
    crate::leanh::lean_dec(v_a_4034_);
    crate::leanh::lean_dec_ref(v_a_4033_);
    crate::leanh::lean_dec(v_a_4032_);
    crate::leanh::lean_dec_ref(v_a_4031_);
    crate::leanh::lean_dec(v_a_4030_);
    crate::leanh::lean_dec_ref(v_a_4029_);
    crate::leanh::lean_dec(v_a_4028_);
    crate::leanh::lean_dec(v_a_4027_);
    crate::leanh::lean_dec(v_a_4026_);
    crate::leanh::lean_dec_ref(v_k_4025_);
    return v_res_4038_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(
    mut v_u_4045_: *mut crate::leanh::LeanObject,
    mut v_h_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
    mut v_a_4049_: *mut crate::leanh::LeanObject,
    mut v_a_4050_: *mut crate::leanh::LeanObject,
    mut v_a_4051_: *mut crate::leanh::LeanObject,
    mut v_a_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4059_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1;
                v___x_4060_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_4059_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
                if crate::leanh::lean_obj_tag(v___x_4060_) == 0 {
                    v_a_4061_ = crate::leanh::lean_ctor_get(v___x_4060_, 0);
                    v_isSharedCheck_4069_ = (!crate::leanh::lean_is_exclusive(v___x_4060_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v___x_4063_ = v___x_4060_;
                        v_isShared_4064_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4061_);
                        crate::leanh::lean_dec(v___x_4060_);
                        v___x_4063_ = crate::leanh::lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_4046_);
                    crate::leanh::lean_dec_ref(v_u_4045_);
                    return v___x_4060_;
                }
            }
            1 => {
                v___x_4065_ = l_Lean_mkAppB(v_a_4061_, v_u_4045_, v_h_4046_);
                if v_isShared_4064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4063_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
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
    mut v_u_4070_: *mut crate::leanh::LeanObject,
    mut v_h_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
    mut v_a_4073_: *mut crate::leanh::LeanObject,
    mut v_a_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
    mut v_a_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_4070_, v_h_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
    crate::leanh::lean_dec(v_a_4082_);
    crate::leanh::lean_dec_ref(v_a_4081_);
    crate::leanh::lean_dec(v_a_4080_);
    crate::leanh::lean_dec_ref(v_a_4079_);
    crate::leanh::lean_dec(v_a_4078_);
    crate::leanh::lean_dec_ref(v_a_4077_);
    crate::leanh::lean_dec(v_a_4076_);
    crate::leanh::lean_dec_ref(v_a_4075_);
    crate::leanh::lean_dec(v_a_4074_);
    crate::leanh::lean_dec(v_a_4073_);
    crate::leanh::lean_dec(v_a_4072_);
    return v_res_4084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(
    mut v_u_4097_: *mut crate::leanh::LeanObject,
    mut v_k_4098_: *mut crate::leanh::LeanObject,
    mut v_h_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4119_: u8 = 0;
    let mut v___y_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_4118_ = crate::leanh::lean_ctor_get(v_k_4098_, 0);
                v_strict_4119_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_4098_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                v___x_4117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4116_);
                return v___x_4117_;
            }
            2 => {
                crate::leanh::lean_inc(v___y_4121_);
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
                if crate::leanh::lean_obj_tag(v___x_4122_) == 0 {
                    v_a_4123_ = crate::leanh::lean_ctor_get(v___x_4122_, 0);
                    crate::leanh::lean_inc(v_a_4123_);
                    crate::leanh::lean_dec_ref_known(v___x_4122_, 1);
                    v___x_4124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_4125_ = lean_int_dec_le(v___x_4124_, v_k_4118_);
                    if v___x_4125_ == 0 {
                        v___x_4126_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_4127_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_4128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_4129_ = lean_int_neg(v_k_4118_);
                        v___x_4130_ = l_Int_toNat(v___x_4129_);
                        crate::leanh::lean_dec(v___x_4129_);
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
                    crate::leanh::lean_dec_ref(v_h_4099_);
                    crate::leanh::lean_dec_ref(v_u_4097_);
                    return v___x_4122_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset___boxed(
    mut v_u_4137_: *mut crate::leanh::LeanObject,
    mut v_k_4138_: *mut crate::leanh::LeanObject,
    mut v_h_4139_: *mut crate::leanh::LeanObject,
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v_a_4145_: *mut crate::leanh::LeanObject,
    mut v_a_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v_a_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_4137_, v_k_4138_, v_h_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
    crate::leanh::lean_dec(v_a_4150_);
    crate::leanh::lean_dec_ref(v_a_4149_);
    crate::leanh::lean_dec(v_a_4148_);
    crate::leanh::lean_dec_ref(v_a_4147_);
    crate::leanh::lean_dec(v_a_4146_);
    crate::leanh::lean_dec_ref(v_a_4145_);
    crate::leanh::lean_dec(v_a_4144_);
    crate::leanh::lean_dec_ref(v_a_4143_);
    crate::leanh::lean_dec(v_a_4142_);
    crate::leanh::lean_dec(v_a_4141_);
    crate::leanh::lean_dec(v_a_4140_);
    crate::leanh::lean_dec_ref(v_k_4138_);
    return v_res_4152_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkSelfUnsatProof(
    mut v_u_4153_: *mut crate::leanh::LeanObject,
    mut v_k_4154_: *mut crate::leanh::LeanObject,
    mut v_h_4155_: *mut crate::leanh::LeanObject,
    mut v_a_4156_: *mut crate::leanh::LeanObject,
    mut v_a_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4168_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_,
                    v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_,
                );
                if crate::leanh::lean_obj_tag(v___x_4168_) == 0 {
                    v_a_4169_ = crate::leanh::lean_ctor_get(v___x_4168_, 0);
                    crate::leanh::lean_inc(v_a_4169_);
                    crate::leanh::lean_dec_ref_known(v___x_4168_, 1);
                    v___x_4170_ = (crate::leanh::lean_unbox(v_a_4169_) as u8);
                    crate::leanh::lean_dec(v_a_4169_);
                    if v___x_4170_ == 0 {
                        v___x_4171_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore(v_u_4153_, v_h_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                        return v___x_4171_;
                    } else {
                        v___x_4172_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofOffset(v_u_4153_, v_k_4154_, v_h_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                        return v___x_4172_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_4155_);
                    crate::leanh::lean_dec_ref(v_u_4153_);
                    v_a_4173_ = crate::leanh::lean_ctor_get(v___x_4168_, 0);
                    v_isSharedCheck_4180_ = (!crate::leanh::lean_is_exclusive(v___x_4168_)) as u8;
                    if v_isSharedCheck_4180_ == 0 {
                        v___x_4175_ = v___x_4168_;
                        v_isShared_4176_ = v_isSharedCheck_4180_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4173_);
                        crate::leanh::lean_dec(v___x_4168_);
                        v___x_4175_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
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
    mut v_u_4181_: *mut crate::leanh::LeanObject,
    mut v_k_4182_: *mut crate::leanh::LeanObject,
    mut v_h_4183_: *mut crate::leanh::LeanObject,
    mut v_a_4184_: *mut crate::leanh::LeanObject,
    mut v_a_4185_: *mut crate::leanh::LeanObject,
    mut v_a_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
    mut v_a_4190_: *mut crate::leanh::LeanObject,
    mut v_a_4191_: *mut crate::leanh::LeanObject,
    mut v_a_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4196_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(
        v_u_4181_, v_k_4182_, v_h_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_,
        v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_,
    );
    crate::leanh::lean_dec(v_a_4194_);
    crate::leanh::lean_dec_ref(v_a_4193_);
    crate::leanh::lean_dec(v_a_4192_);
    crate::leanh::lean_dec_ref(v_a_4191_);
    crate::leanh::lean_dec(v_a_4190_);
    crate::leanh::lean_dec_ref(v_a_4189_);
    crate::leanh::lean_dec(v_a_4188_);
    crate::leanh::lean_dec_ref(v_a_4187_);
    crate::leanh::lean_dec(v_a_4186_);
    crate::leanh::lean_dec(v_a_4185_);
    crate::leanh::lean_dec(v_a_4184_);
    crate::leanh::lean_dec_ref(v_k_4182_);
    return v_res_4196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4199_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__1;
    v___x_4200_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4201_ = crate::leanh::lean_unsigned_to_nat(255);
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
    mut v_u_4205_: *mut crate::leanh::LeanObject,
    mut v_v_4206_: *mut crate::leanh::LeanObject,
    mut v_k_u2081_4207_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4208_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_4209_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_a_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_strict_4223_: u8 = 0;
    let mut v_strict_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_strict_4223_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_u2081_4207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_strict_4224_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_u2082_4209_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_inc_ref_n(v_u_4205_, 2);
                v___x_4225_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCoreProof(v_u_4205_, v_v_4206_, v_u_4205_, v_strict_4223_, v_strict_4224_, v_h_u2081_4208_, v_h_u2082_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
                if crate::leanh::lean_obj_tag(v___x_4225_) == 0 {
                    v_a_4226_ = crate::leanh::lean_ctor_get(v___x_4225_, 0);
                    crate::leanh::lean_inc(v_a_4226_);
                    crate::leanh::lean_dec_ref_known(v___x_4225_, 1);
                    if v_strict_4223_ == 0 {
                        if v_strict_4224_ == 0 {
                            crate::leanh::lean_dec(v_a_4226_);
                            crate::leanh::lean_dec_ref(v_u_4205_);
                            v___x_4239_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore___closed__2);
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
                    crate::leanh::lean_dec_ref(v_u_4205_);
                    return v___x_4225_;
                }
            }
            1 => {
                v___x_4228_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkSelfUnsatProofCore___closed__1;
                v___x_4229_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLeLtPreorderPrefix(v___x_4228_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
                if crate::leanh::lean_obj_tag(v___x_4229_) == 0 {
                    v_a_4230_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                    v_isSharedCheck_4238_ = (!crate::leanh::lean_is_exclusive(v___x_4229_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4232_ = v___x_4229_;
                        v_isShared_4233_ = v_isSharedCheck_4238_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4230_);
                        crate::leanh::lean_dec(v___x_4229_);
                        v___x_4232_ = crate::leanh::lean_box(0);
                        v_isShared_4233_ = v_isSharedCheck_4238_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4226_);
                    crate::leanh::lean_dec_ref(v_u_4205_);
                    return v___x_4229_;
                }
            }
            2 => {
                v___x_4234_ = l_Lean_mkAppB(v_a_4230_, v_u_4205_, v_a_4226_);
                if v_isShared_4233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4232_, 0, v___x_4234_);
                    v___x_4236_ = v___x_4232_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_4241_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_4242_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_u2081_4243_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_h_u2081_4244_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_u2082_4245_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_h_u2082_4246_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4247_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4248_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4249_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4250_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4251_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4252_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4253_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4254_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4255_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4256_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4257_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_4258_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4257_);
    crate::leanh::lean_dec_ref(v_a_4256_);
    crate::leanh::lean_dec(v_a_4255_);
    crate::leanh::lean_dec_ref(v_a_4254_);
    crate::leanh::lean_dec(v_a_4253_);
    crate::leanh::lean_dec_ref(v_a_4252_);
    crate::leanh::lean_dec(v_a_4251_);
    crate::leanh::lean_dec_ref(v_a_4250_);
    crate::leanh::lean_dec(v_a_4249_);
    crate::leanh::lean_dec(v_a_4248_);
    crate::leanh::lean_dec(v_a_4247_);
    crate::leanh::lean_dec_ref(v_k_u2082_4245_);
    crate::leanh::lean_dec_ref(v_k_u2081_4243_);
    return v_res_4259_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(
    mut v_u_4260_: *mut crate::leanh::LeanObject,
    mut v_v_4261_: *mut crate::leanh::LeanObject,
    mut v_k_u2081_4262_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4263_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_4264_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___y_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4292_: u8 = 0;
    let mut v___y_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4312_: u8 = 0;
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref_n(v_u_4260_, 2);
                v___x_4278_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof(v_u_4260_, v_v_4261_, v_u_4260_, v_k_u2081_4262_, v_k_u2082_4264_, v_h_u2081_4263_, v_h_u2082_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
                if crate::leanh::lean_obj_tag(v___x_4278_) == 0 {
                    v_a_4279_ = crate::leanh::lean_ctor_get(v___x_4278_, 0);
                    v_isSharedCheck_4314_ = (!crate::leanh::lean_is_exclusive(v___x_4278_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v___x_4281_ = v___x_4278_;
                        v_isShared_4282_ = v_isSharedCheck_4314_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4279_);
                        crate::leanh::lean_dec(v___x_4278_);
                        v___x_4281_ = crate::leanh::lean_box(0);
                        v_isShared_4282_ = v_isSharedCheck_4314_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_u_4260_);
                    return v___x_4278_;
                }
            }
            1 => {
                v_k_4291_ = crate::leanh::lean_ctor_get(v_k_u2081_4262_, 0);
                v_strict_4292_ = crate::leanh::lean_ctor_get_uint8(
                    v_k_u2081_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_strict_4292_ == 0 {
                    v_strict_4312_ = crate::leanh::lean_ctor_get_uint8(
                        v_k_u2082_4264_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    crate::leanh::lean_ctor_set(v___x_4281_, 0, v___x_4287_);
                    v___x_4289_ = v___x_4281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4289_;
            }
            4 => {
                crate::leanh::lean_inc(v___y_4294_);
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
                if crate::leanh::lean_obj_tag(v___x_4295_) == 0 {
                    v_a_4296_ = crate::leanh::lean_ctor_get(v___x_4295_, 0);
                    crate::leanh::lean_inc(v_a_4296_);
                    crate::leanh::lean_dec_ref_known(v___x_4295_, 1);
                    v_k_4297_ = crate::leanh::lean_ctor_get(v_k_u2082_4264_, 0);
                    v___x_4298_ = lean_int_add(v_k_4291_, v_k_4297_);
                    v___x_4299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransCore___closed__0);
                    v___x_4300_ = lean_int_dec_le(v___x_4299_, v___x_4298_);
                    if v___x_4300_ == 0 {
                        v___x_4301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__5);
                        v___x_4302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__8);
                        v___x_4303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkTransOffsetProof___closed__11);
                        v___x_4304_ = lean_int_neg(v___x_4298_);
                        crate::leanh::lean_dec(v___x_4298_);
                        v___x_4305_ = l_Int_toNat(v___x_4304_);
                        crate::leanh::lean_dec(v___x_4304_);
                        v___x_4306_ = l_Lean_instToExprInt_mkNat(v___x_4305_);
                        v___x_4307_ =
                            l_Lean_mkApp3(v___x_4301_, v___x_4302_, v___x_4303_, v___x_4306_);
                        v___y_4284_ = v_a_4296_;
                        v___y_4285_ = v___x_4307_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4308_ = l_Int_toNat(v___x_4298_);
                        crate::leanh::lean_dec(v___x_4298_);
                        v___x_4309_ = l_Lean_instToExprInt_mkNat(v___x_4308_);
                        v___y_4284_ = v_a_4296_;
                        v___y_4285_ = v___x_4309_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4281_);
                    crate::leanh::lean_dec(v_a_4279_);
                    crate::leanh::lean_dec_ref(v_u_4260_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_4315_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_4316_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_u2081_4317_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_h_u2081_4318_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_u2082_4319_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_h_u2082_4320_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4321_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4322_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4323_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4324_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4325_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4326_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4327_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4328_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4329_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4330_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4331_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_4332_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4331_);
    crate::leanh::lean_dec_ref(v_a_4330_);
    crate::leanh::lean_dec(v_a_4329_);
    crate::leanh::lean_dec_ref(v_a_4328_);
    crate::leanh::lean_dec(v_a_4327_);
    crate::leanh::lean_dec_ref(v_a_4326_);
    crate::leanh::lean_dec(v_a_4325_);
    crate::leanh::lean_dec_ref(v_a_4324_);
    crate::leanh::lean_dec(v_a_4323_);
    crate::leanh::lean_dec(v_a_4322_);
    crate::leanh::lean_dec(v_a_4321_);
    crate::leanh::lean_dec_ref(v_k_u2082_4319_);
    crate::leanh::lean_dec_ref(v_k_u2081_4317_);
    return v_res_4333_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkUnsatProof(
    mut v_u_4334_: *mut crate::leanh::LeanObject,
    mut v_v_4335_: *mut crate::leanh::LeanObject,
    mut v_k_u2081_4336_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4337_: *mut crate::leanh::LeanObject,
    mut v_k_u2082_4338_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_a_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
    mut v_a_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4352_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_,
                    v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_,
                );
                if crate::leanh::lean_obj_tag(v___x_4352_) == 0 {
                    v_a_4353_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                    crate::leanh::lean_inc(v_a_4353_);
                    crate::leanh::lean_dec_ref_known(v___x_4352_, 1);
                    v___x_4354_ = (crate::leanh::lean_unbox(v_a_4353_) as u8);
                    crate::leanh::lean_dec(v_a_4353_);
                    if v___x_4354_ == 0 {
                        v___x_4355_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofCore(v_u_4334_, v_v_4335_, v_k_u2081_4336_, v_h_u2081_4337_, v_k_u2082_4338_, v_h_u2082_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
                        return v___x_4355_;
                    } else {
                        v___x_4356_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkUnsatProofOffset(v_u_4334_, v_v_4335_, v_k_u2081_4336_, v_h_u2081_4337_, v_k_u2082_4338_, v_h_u2082_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
                        return v___x_4356_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2082_4339_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4337_);
                    crate::leanh::lean_dec_ref(v_v_4335_);
                    crate::leanh::lean_dec_ref(v_u_4334_);
                    v_a_4357_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                    v_isSharedCheck_4364_ = (!crate::leanh::lean_is_exclusive(v___x_4352_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4359_ = v___x_4352_;
                        v_isShared_4360_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4357_);
                        crate::leanh::lean_dec(v___x_4352_);
                        v___x_4359_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_4365_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_4366_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_u2081_4367_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_h_u2081_4368_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_u2082_4369_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_h_u2082_4370_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4371_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4372_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4373_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4374_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4375_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4376_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4377_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4378_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4379_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4380_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4381_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_4382_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4381_);
    crate::leanh::lean_dec_ref(v_a_4380_);
    crate::leanh::lean_dec(v_a_4379_);
    crate::leanh::lean_dec_ref(v_a_4378_);
    crate::leanh::lean_dec(v_a_4377_);
    crate::leanh::lean_dec_ref(v_a_4376_);
    crate::leanh::lean_dec(v_a_4375_);
    crate::leanh::lean_dec_ref(v_a_4374_);
    crate::leanh::lean_dec(v_a_4373_);
    crate::leanh::lean_dec(v_a_4372_);
    crate::leanh::lean_dec(v_a_4371_);
    crate::leanh::lean_dec_ref(v_k_u2082_4369_);
    crate::leanh::lean_dec_ref(v_k_u2081_4367_);
    return v_res_4383_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore(
    mut v_u_4390_: *mut crate::leanh::LeanObject,
    mut v_v_4391_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4392_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
    mut v_a_4400_: *mut crate::leanh::LeanObject,
    mut v_a_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4406_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeCore___closed__1;
                v___x_4407_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_4406_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
                if crate::leanh::lean_obj_tag(v___x_4407_) == 0 {
                    v_a_4408_ = crate::leanh::lean_ctor_get(v___x_4407_, 0);
                    v_isSharedCheck_4416_ = (!crate::leanh::lean_is_exclusive(v___x_4407_)) as u8;
                    if v_isSharedCheck_4416_ == 0 {
                        v___x_4410_ = v___x_4407_;
                        v_isShared_4411_ = v_isSharedCheck_4416_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4408_);
                        crate::leanh::lean_dec(v___x_4407_);
                        v___x_4410_ = crate::leanh::lean_box(0);
                        v_isShared_4411_ = v_isSharedCheck_4416_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2082_4393_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4392_);
                    crate::leanh::lean_dec_ref(v_v_4391_);
                    crate::leanh::lean_dec_ref(v_u_4390_);
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
                    crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4412_);
                    v___x_4414_ = v___x_4410_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
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
    mut v_u_4417_: *mut crate::leanh::LeanObject,
    mut v_v_4418_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4419_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_a_4431_: *mut crate::leanh::LeanObject,
    mut v_a_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4431_);
    crate::leanh::lean_dec_ref(v_a_4430_);
    crate::leanh::lean_dec(v_a_4429_);
    crate::leanh::lean_dec_ref(v_a_4428_);
    crate::leanh::lean_dec(v_a_4427_);
    crate::leanh::lean_dec_ref(v_a_4426_);
    crate::leanh::lean_dec(v_a_4425_);
    crate::leanh::lean_dec_ref(v_a_4424_);
    crate::leanh::lean_dec(v_a_4423_);
    crate::leanh::lean_dec(v_a_4422_);
    crate::leanh::lean_dec(v_a_4421_);
    return v_res_4433_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset(
    mut v_u_4440_: *mut crate::leanh::LeanObject,
    mut v_v_4441_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4442_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4443_: *mut crate::leanh::LeanObject,
    mut v_a_4444_: *mut crate::leanh::LeanObject,
    mut v_a_4445_: *mut crate::leanh::LeanObject,
    mut v_a_4446_: *mut crate::leanh::LeanObject,
    mut v_a_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
    mut v_a_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
    mut v_a_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___y_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4456_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLeOffset___closed__1;
                v___x_4457_ = l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix(v___x_4456_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    crate::leanh::lean_inc(v_a_4458_);
                    crate::leanh::lean_dec_ref_known(v___x_4457_, 1);
                    v___x_4459_ = l_Lean_Meta_Grind_Order_getStruct(
                        v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_,
                        v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4459_) == 0 {
                        v_a_4460_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4475_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v___x_4462_ = v___x_4459_;
                            v_isShared_4463_ = v_isSharedCheck_4475_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4460_);
                            crate::leanh::lean_dec(v___x_4459_);
                            v___x_4462_ = crate::leanh::lean_box(0);
                            v_isShared_4463_ = v_isSharedCheck_4475_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4458_);
                        crate::leanh::lean_dec_ref(v_h_u2082_4443_);
                        crate::leanh::lean_dec_ref(v_h_u2081_4442_);
                        crate::leanh::lean_dec_ref(v_v_4441_);
                        crate::leanh::lean_dec_ref(v_u_4440_);
                        v_a_4476_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4483_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4478_ = v___x_4459_;
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4476_);
                            crate::leanh::lean_dec(v___x_4459_);
                            v___x_4478_ = crate::leanh::lean_box(0);
                            v_isShared_4479_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2082_4443_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4442_);
                    crate::leanh::lean_dec_ref(v_v_4441_);
                    crate::leanh::lean_dec_ref(v_u_4440_);
                    return v___x_4457_;
                }
            }
            1 => {
                v_ringInst_x3f_4471_ = crate::leanh::lean_ctor_get(v_a_4460_, 10);
                crate::leanh::lean_inc(v_ringInst_x3f_4471_);
                crate::leanh::lean_dec(v_a_4460_);
                if crate::leanh::lean_obj_tag(v_ringInst_x3f_4471_) == 0 {
                    v___x_4472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix___closed__3);
                    v___x_4473_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkLePartialPrefix_spec__0(v___x_4472_);
                    v___y_4465_ = v___x_4473_;
                    state = 2;
                    continue;
                } else {
                    v_val_4474_ = crate::leanh::lean_ctor_get(v_ringInst_x3f_4471_, 0);
                    crate::leanh::lean_inc(v_val_4474_);
                    crate::leanh::lean_dec_ref_known(v_ringInst_x3f_4471_, 1);
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
                    crate::leanh::lean_ctor_set(v___x_4462_, 0, v___x_4467_);
                    v___x_4469_ = v___x_4462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
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
                    v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
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
    mut v_u_4484_: *mut crate::leanh::LeanObject,
    mut v_v_4485_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4486_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
    mut v_a_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
    mut v_a_4495_: *mut crate::leanh::LeanObject,
    mut v_a_4496_: *mut crate::leanh::LeanObject,
    mut v_a_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4498_);
    crate::leanh::lean_dec_ref(v_a_4497_);
    crate::leanh::lean_dec(v_a_4496_);
    crate::leanh::lean_dec_ref(v_a_4495_);
    crate::leanh::lean_dec(v_a_4494_);
    crate::leanh::lean_dec_ref(v_a_4493_);
    crate::leanh::lean_dec(v_a_4492_);
    crate::leanh::lean_dec_ref(v_a_4491_);
    crate::leanh::lean_dec(v_a_4490_);
    crate::leanh::lean_dec(v_a_4489_);
    crate::leanh::lean_dec(v_a_4488_);
    return v_res_4500_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(
    mut v_u_4501_: *mut crate::leanh::LeanObject,
    mut v_v_4502_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4503_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4504_: *mut crate::leanh::LeanObject,
    mut v_a_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
    mut v_a_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_a_4514_: *mut crate::leanh::LeanObject,
    mut v_a_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4517_ = l_Lean_Meta_Grind_Order_isRing(
                    v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_,
                    v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_,
                );
                if crate::leanh::lean_obj_tag(v___x_4517_) == 0 {
                    v_a_4518_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
                    crate::leanh::lean_inc(v_a_4518_);
                    crate::leanh::lean_dec_ref_known(v___x_4517_, 1);
                    v___x_4519_ = (crate::leanh::lean_unbox(v_a_4518_) as u8);
                    crate::leanh::lean_dec(v_a_4518_);
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
                    crate::leanh::lean_dec_ref(v_h_u2082_4504_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4503_);
                    crate::leanh::lean_dec_ref(v_v_4502_);
                    crate::leanh::lean_dec_ref(v_u_4501_);
                    v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
                    v_isSharedCheck_4529_ = (!crate::leanh::lean_is_exclusive(v___x_4517_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4524_ = v___x_4517_;
                        v_isShared_4525_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4522_);
                        crate::leanh::lean_dec(v___x_4517_);
                        v___x_4524_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
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
    mut v_u_4530_: *mut crate::leanh::LeanObject,
    mut v_v_4531_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4532_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
    mut v_a_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4544_);
    crate::leanh::lean_dec_ref(v_a_4543_);
    crate::leanh::lean_dec(v_a_4542_);
    crate::leanh::lean_dec_ref(v_a_4541_);
    crate::leanh::lean_dec(v_a_4540_);
    crate::leanh::lean_dec_ref(v_a_4539_);
    crate::leanh::lean_dec(v_a_4538_);
    crate::leanh::lean_dec_ref(v_a_4537_);
    crate::leanh::lean_dec(v_a_4536_);
    crate::leanh::lean_dec(v_a_4535_);
    crate::leanh::lean_dec(v_a_4534_);
    return v_res_4546_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Proof(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
}
