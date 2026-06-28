// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.StructId
// Imports: Lean.Meta.Tactic.Grind.Order.Types Lean.Meta.Tactic.Grind.OrderInsts Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_instInhabitedExpr, l_Lean_mkApp5, l_Lean_mkAppB,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_getDecLevel_x3f;
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommRingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
    l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing;
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::Types::{
    initialize_Lean_Meta_Tactic_Grind_Order_Types, l_Lean_Meta_Grind_Order_get_x27___redArg,
    l_Lean_Meta_Grind_Order_orderExt, runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::OrderInsts::{
    initialize_Lean_Meta_Tactic_Grind_OrderInsts,
    l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg,
    l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg,
    l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg,
    l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_getConfig___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_panic_fn_borrowed,
};
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 114, 100, 101, 114, 101, 100, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject,17867769263165242357 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,8347582161988589016 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject,17878876274162330439 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,8347582161988589016 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject,7316284823769321069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject,17878876274162330439 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__10_value) as *mut crate::leanh::LeanObject,11833570877100518198 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(
    mut v_e_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
    mut v_a_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
    mut v_a_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_Sym_canon(
        v_e_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_,
    );
    if crate::leanh::lean_obj_tag(v___x_1003_) == 0 {
        let mut v_a_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1004_ = crate::leanh::lean_ctor_get(v___x_1003_, 0);
        crate::leanh::lean_inc(v_a_1004_);
        crate::leanh::lean_dec_ref_known(v___x_1003_, 1);
        v___x_1005_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1004_, v_a_997_);
        return v___x_1005_;
    } else {
        return v___x_1003_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg___boxed(
    mut v_e_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
    crate::leanh::lean_dec(v_a_1012_);
    crate::leanh::lean_dec_ref(v_a_1011_);
    crate::leanh::lean_dec(v_a_1010_);
    crate::leanh::lean_dec_ref(v_a_1009_);
    crate::leanh::lean_dec(v_a_1008_);
    crate::leanh::lean_dec_ref(v_a_1007_);
    return v_res_1014_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(
    mut v_e_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_e_1015_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
    return v___x_1027_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___boxed(
    mut v_e_1028_: *mut crate::leanh::LeanObject,
    mut v_a_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
    mut v_a_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
    mut v_a_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1040_ =
        l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess(
            v_e_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_,
            v_a_1036_, v_a_1037_, v_a_1038_,
        );
    crate::leanh::lean_dec(v_a_1038_);
    crate::leanh::lean_dec_ref(v_a_1037_);
    crate::leanh::lean_dec(v_a_1036_);
    crate::leanh::lean_dec_ref(v_a_1035_);
    crate::leanh::lean_dec(v_a_1034_);
    crate::leanh::lean_dec_ref(v_a_1033_);
    crate::leanh::lean_dec(v_a_1032_);
    crate::leanh::lean_dec_ref(v_a_1031_);
    crate::leanh::lean_dec(v_a_1030_);
    crate::leanh::lean_dec(v_a_1029_);
    return v_res_1040_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg(
    mut v_fn_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_fn_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
    return v___x_1049_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg___boxed(
    mut v_fn_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
    mut v_a_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
    mut v_a_1056_: *mut crate::leanh::LeanObject,
    mut v_a_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1058_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___redArg(v_fn_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
    crate::leanh::lean_dec(v_a_1056_);
    crate::leanh::lean_dec_ref(v_a_1055_);
    crate::leanh::lean_dec(v_a_1054_);
    crate::leanh::lean_dec_ref(v_a_1053_);
    crate::leanh::lean_dec(v_a_1052_);
    crate::leanh::lean_dec_ref(v_a_1051_);
    return v_res_1058_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(
    mut v_fn_1059_: *mut crate::leanh::LeanObject,
    mut v_a_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_a_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v_fn_1059_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
    return v___x_1071_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn___boxed(
    mut v_fn_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ =
        l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_internalizeFn(
            v_fn_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_,
            v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_,
        );
    crate::leanh::lean_dec(v_a_1082_);
    crate::leanh::lean_dec_ref(v_a_1081_);
    crate::leanh::lean_dec(v_a_1080_);
    crate::leanh::lean_dec_ref(v_a_1079_);
    crate::leanh::lean_dec(v_a_1078_);
    crate::leanh::lean_dec_ref(v_a_1077_);
    crate::leanh::lean_dec(v_a_1076_);
    crate::leanh::lean_dec_ref(v_a_1075_);
    crate::leanh::lean_dec(v_a_1074_);
    crate::leanh::lean_dec(v_a_1073_);
    return v_res_1084_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(
    mut v_declName_1085_: *mut crate::leanh::LeanObject,
    mut v_u_1086_: *mut crate::leanh::LeanObject,
    mut v_type_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = crate::leanh::lean_box(0);
    v___x_1094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1094_, 0, v_u_1086_);
    crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
    v___x_1095_ = l_Lean_mkConst(v_declName_1085_, v___x_1094_);
    v___x_1096_ = l_Lean_Expr_app___override(v___x_1095_, v_type_1087_);
    v___x_1097_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v___x_1096_,
        v_a_1088_,
        v_a_1089_,
        v_a_1090_,
        v_a_1091_,
    );
    return v___x_1097_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg___boxed(
    mut v_declName_1098_: *mut crate::leanh::LeanObject,
    mut v_u_1099_: *mut crate::leanh::LeanObject,
    mut v_type_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_1098_, v_u_1099_, v_type_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
    crate::leanh::lean_dec(v_a_1104_);
    crate::leanh::lean_dec_ref(v_a_1103_);
    crate::leanh::lean_dec(v_a_1102_);
    crate::leanh::lean_dec_ref(v_a_1101_);
    return v_res_1106_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(
    mut v_declName_1107_: *mut crate::leanh::LeanObject,
    mut v_u_1108_: *mut crate::leanh::LeanObject,
    mut v_type_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v_declName_1107_, v_u_1108_, v_type_1109_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
    return v___x_1121_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___boxed(
    mut v_declName_1122_: *mut crate::leanh::LeanObject,
    mut v_u_1123_: *mut crate::leanh::LeanObject,
    mut v_type_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ =
        l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f(
            v_declName_1122_,
            v_u_1123_,
            v_type_1124_,
            v_a_1125_,
            v_a_1126_,
            v_a_1127_,
            v_a_1128_,
            v_a_1129_,
            v_a_1130_,
            v_a_1131_,
            v_a_1132_,
            v_a_1133_,
            v_a_1134_,
        );
    crate::leanh::lean_dec(v_a_1134_);
    crate::leanh::lean_dec_ref(v_a_1133_);
    crate::leanh::lean_dec(v_a_1132_);
    crate::leanh::lean_dec_ref(v_a_1131_);
    crate::leanh::lean_dec(v_a_1130_);
    crate::leanh::lean_dec_ref(v_a_1129_);
    crate::leanh::lean_dec(v_a_1128_);
    crate::leanh::lean_dec_ref(v_a_1127_);
    crate::leanh::lean_dec(v_a_1126_);
    crate::leanh::lean_dec(v_a_1125_);
    return v_res_1136_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(
    mut v_u_1144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1145_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1146_: *mut crate::leanh::LeanObject,
    mut v_leInst_1147_: *mut crate::leanh::LeanObject,
    mut v_ltInst_1148_: *mut crate::leanh::LeanObject,
    mut v_isPreorderInst_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___closed__3;
    v___x_1156_ = crate::leanh::lean_box(0);
    v___x_1157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1157_, 0, v_u_1144_);
    crate::leanh::lean_ctor_set(v___x_1157_, 1, v___x_1156_);
    v___x_1158_ = l_Lean_mkConst(v___x_1155_, v___x_1157_);
    v_e_1159_ = l_Lean_mkApp5(
        v___x_1158_,
        v_00_u03b1_1145_,
        v_semiringInst_1146_,
        v_leInst_1147_,
        v_ltInst_1148_,
        v_isPreorderInst_1149_,
    );
    v___x_1160_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_e_1159_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_,
    );
    return v___x_1160_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg___boxed(
    mut v_u_1161_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1162_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1163_: *mut crate::leanh::LeanObject,
    mut v_leInst_1164_: *mut crate::leanh::LeanObject,
    mut v_ltInst_1165_: *mut crate::leanh::LeanObject,
    mut v_isPreorderInst_1166_: *mut crate::leanh::LeanObject,
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1172_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_1161_, v_00_u03b1_1162_, v_semiringInst_1163_, v_leInst_1164_, v_ltInst_1165_, v_isPreorderInst_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
    crate::leanh::lean_dec(v_a_1170_);
    crate::leanh::lean_dec_ref(v_a_1169_);
    crate::leanh::lean_dec(v_a_1168_);
    crate::leanh::lean_dec_ref(v_a_1167_);
    return v_res_1172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(
    mut v_u_1173_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1174_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1175_: *mut crate::leanh::LeanObject,
    mut v_leInst_1176_: *mut crate::leanh::LeanObject,
    mut v_ltInst_1177_: *mut crate::leanh::LeanObject,
    mut v_isPreorderInst_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v_a_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_u_1173_, v_00_u03b1_1174_, v_semiringInst_1175_, v_leInst_1176_, v_ltInst_1177_, v_isPreorderInst_1178_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
    return v___x_1190_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_1191_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_1192_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_semiringInst_1193_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_leInst_1194_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ltInst_1195_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_isPreorderInst_1196_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_1197_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_1198_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_1199_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_1200_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_1201_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_1202_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_1203_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_1204_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_1205_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_1206_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_1207_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f(v_u_1191_, v_00_u03b1_1192_, v_semiringInst_1193_, v_leInst_1194_, v_ltInst_1195_, v_isPreorderInst_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
    crate::leanh::lean_dec(v_a_1206_);
    crate::leanh::lean_dec_ref(v_a_1205_);
    crate::leanh::lean_dec(v_a_1204_);
    crate::leanh::lean_dec_ref(v_a_1203_);
    crate::leanh::lean_dec(v_a_1202_);
    crate::leanh::lean_dec_ref(v_a_1201_);
    crate::leanh::lean_dec(v_a_1200_);
    crate::leanh::lean_dec_ref(v_a_1199_);
    crate::leanh::lean_dec(v_a_1198_);
    crate::leanh::lean_dec(v_a_1197_);
    return v_res_1208_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f_spec__0(
    mut v_msg_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = l_Lean_instInhabitedExpr;
    v___x_1211_ = lean_panic_fn_borrowed(v___x_1210_, v_msg_1209_);
    return v___x_1211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0(
    mut v___x_1212_: *mut crate::leanh::LeanObject,
    mut v_s_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMapInv_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1214_ = crate::leanh::lean_ctor_get(v_s_1213_, 0);
                v_typeIdOf_1215_ = crate::leanh::lean_ctor_get(v_s_1213_, 1);
                v_exprToStructId_1216_ = crate::leanh::lean_ctor_get(v_s_1213_, 2);
                v_termMap_1217_ = crate::leanh::lean_ctor_get(v_s_1213_, 3);
                v_termMapInv_1218_ = crate::leanh::lean_ctor_get(v_s_1213_, 4);
                v_isSharedCheck_1226_ = (!crate::leanh::lean_is_exclusive(v_s_1213_)) as u8;
                if v_isSharedCheck_1226_ == 0 {
                    v___x_1220_ = v_s_1213_;
                    v_isShared_1221_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_termMapInv_1218_);
                    crate::leanh::lean_inc(v_termMap_1217_);
                    crate::leanh::lean_inc(v_exprToStructId_1216_);
                    crate::leanh::lean_inc(v_typeIdOf_1215_);
                    crate::leanh::lean_inc(v_structs_1214_);
                    crate::leanh::lean_dec(v_s_1213_);
                    v___x_1220_ = crate::leanh::lean_box(0);
                    v_isShared_1221_ = v_isSharedCheck_1226_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1222_ = lean_array_push(v_structs_1214_, v___x_1212_);
                if v_isShared_1221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1222_);
                    v___x_1224_ = v___x_1220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_typeIdOf_1215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_exprToStructId_1216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_termMap_1217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_termMapInv_1218_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(
    mut v_____do__lift_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
    mut v___y_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toRing_1240_ = crate::leanh::lean_ctor_get(v_____do__lift_1227_, 0);
    crate::leanh::lean_inc_ref(v_toRing_1240_);
    v___x_1241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1241_, 0, v_toRing_1240_);
    return v___x_1241_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1___boxed(
    mut v_____do__lift_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_____do__lift_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
    crate::leanh::lean_dec(v___y_1253_);
    crate::leanh::lean_dec_ref(v___y_1252_);
    crate::leanh::lean_dec(v___y_1251_);
    crate::leanh::lean_dec_ref(v___y_1250_);
    crate::leanh::lean_dec(v___y_1249_);
    crate::leanh::lean_dec_ref(v___y_1248_);
    crate::leanh::lean_dec(v___y_1247_);
    crate::leanh::lean_dec_ref(v___y_1246_);
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    crate::leanh::lean_dec_ref(v_____do__lift_1242_);
    return v_res_1255_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1266_);
    v___x_1268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: usize = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = 5usize;
    v___x_1270_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1271_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1272_ = lean_mk_empty_array_with_capacity(v___x_1271_);
    v___x_1273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__6);
    v___x_1274_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1274_, 0, v___x_1273_);
    crate::leanh::lean_ctor_set(v___x_1274_, 1, v___x_1272_);
    crate::leanh::lean_ctor_set(v___x_1274_, 2, v___x_1270_);
    crate::leanh::lean_ctor_set(v___x_1274_, 3, v___x_1270_);
    crate::leanh::lean_ctor_set_usize(v___x_1274_, 4, v___x_1269_);
    return v___x_1274_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__8);
    v___x_1277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(
    mut v_type_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
    mut v_a_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1298_: u8 = 0;
    let mut v_val_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v_val_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v_val_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1339_: u8 = 0;
    let mut v___y_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1354_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_unused_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1366_: u8 = 0;
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v_fst_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v_val_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: u8 = 0;
    let mut v_val_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1412_: u8 = 0;
    let mut v_ringInst_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v_a_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v_a_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1445_: u8 = 0;
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v_val_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v_a_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_a_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_reuseFailAlloc_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_a_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_a_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_a_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1553_: u8 = 0;
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_a_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_1282_);
                v___x_1294_ = l_Lean_Meta_getDecLevel_x3f(
                    v_type_1282_,
                    v_a_1289_,
                    v_a_1290_,
                    v_a_1291_,
                    v_a_1292_,
                );
                if crate::leanh::lean_obj_tag(v___x_1294_) == 0 {
                    v_a_1295_ = crate::leanh::lean_ctor_get(v___x_1294_, 0);
                    v_isSharedCheck_1572_ = (!crate::leanh::lean_is_exclusive(v___x_1294_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1297_ = v___x_1294_;
                        v_isShared_1298_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1295_);
                        crate::leanh::lean_dec(v___x_1294_);
                        v___x_1297_ = crate::leanh::lean_box(0);
                        v_isShared_1298_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v_a_1573_ = crate::leanh::lean_ctor_get(v___x_1294_, 0);
                    v_isSharedCheck_1580_ = (!crate::leanh::lean_is_exclusive(v___x_1294_)) as u8;
                    if v_isSharedCheck_1580_ == 0 {
                        v___x_1575_ = v___x_1294_;
                        v_isShared_1576_ = v_isSharedCheck_1580_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1573_);
                        crate::leanh::lean_dec(v___x_1294_);
                        v___x_1575_ = crate::leanh::lean_box(0);
                        v_isShared_1576_ = v_isSharedCheck_1580_;
                        state = 51;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1295_) == 1 {
                    crate::leanh::lean_del_object(v___x_1297_);
                    v_val_1299_ = crate::leanh::lean_ctor_get(v_a_1295_, 0);
                    v_isSharedCheck_1567_ = (!crate::leanh::lean_is_exclusive(v_a_1295_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1301_ = v_a_1295_;
                        v_isShared_1302_ = v_isSharedCheck_1567_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1299_);
                        crate::leanh::lean_dec(v_a_1295_);
                        v___x_1301_ = crate::leanh::lean_box(0);
                        v_isShared_1302_ = v_isSharedCheck_1567_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1295_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v___x_1568_ = crate::leanh::lean_box(0);
                    if v_isShared_1298_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1297_, 0, v___x_1568_);
                        v___x_1570_ = v___x_1297_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_1571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
                        v___x_1570_ = v_reuseFailAlloc_1571_;
                        state = 50;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1303_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__1;
                crate::leanh::lean_inc_ref(v_type_1282_);
                crate::leanh::lean_inc(v_val_1299_);
                v___x_1304_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_1303_, v_val_1299_, v_type_1282_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                if crate::leanh::lean_obj_tag(v___x_1304_) == 0 {
                    v_a_1305_ = crate::leanh::lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1558_ = (!crate::leanh::lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1558_ == 0 {
                        v___x_1307_ = v___x_1304_;
                        v_isShared_1308_ = v_isSharedCheck_1558_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1305_);
                        crate::leanh::lean_dec(v___x_1304_);
                        v___x_1307_ = crate::leanh::lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1558_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1301_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1566_ = (!crate::leanh::lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1566_ == 0 {
                        v___x_1561_ = v___x_1304_;
                        v_isShared_1562_ = v_isSharedCheck_1566_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1559_);
                        crate::leanh::lean_dec(v___x_1304_);
                        v___x_1561_ = crate::leanh::lean_box(0);
                        v_isShared_1562_ = v_isSharedCheck_1566_;
                        state = 48;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1305_) == 1 {
                    crate::leanh::lean_del_object(v___x_1307_);
                    v_val_1309_ = crate::leanh::lean_ctor_get(v_a_1305_, 0);
                    crate::leanh::lean_inc(v_val_1309_);
                    crate::leanh::lean_inc_ref(v_a_1305_);
                    crate::leanh::lean_inc_ref(v_type_1282_);
                    crate::leanh::lean_inc(v_val_1299_);
                    v___x_1310_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(
                        v_val_1299_,
                        v_type_1282_,
                        v_a_1305_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                        v_a_1292_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1310_) == 0 {
                        v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1545_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1545_ == 0 {
                            v___x_1313_ = v___x_1310_;
                            v_isShared_1314_ = v_isSharedCheck_1545_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1311_);
                            crate::leanh::lean_dec(v___x_1310_);
                            v___x_1313_ = crate::leanh::lean_box(0);
                            v_isShared_1314_ = v_isSharedCheck_1545_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                        crate::leanh::lean_dec(v_val_1309_);
                        crate::leanh::lean_del_object(v___x_1301_);
                        crate::leanh::lean_dec(v_val_1299_);
                        crate::leanh::lean_dec_ref(v_type_1282_);
                        v_a_1546_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1553_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1553_ == 0 {
                            v___x_1548_ = v___x_1310_;
                            v_isShared_1549_ = v_isSharedCheck_1553_;
                            state = 45;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1546_);
                            crate::leanh::lean_dec(v___x_1310_);
                            v___x_1548_ = crate::leanh::lean_box(0);
                            v_isShared_1549_ = v_isSharedCheck_1553_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1305_);
                    crate::leanh::lean_del_object(v___x_1301_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v___x_1554_ = crate::leanh::lean_box(0);
                    if v_isShared_1308_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1307_, 0, v___x_1554_);
                        v___x_1556_ = v___x_1307_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_1557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
                        v___x_1556_ = v_reuseFailAlloc_1557_;
                        state = 47;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1311_) == 1 {
                    crate::leanh::lean_del_object(v___x_1313_);
                    v_val_1315_ = crate::leanh::lean_ctor_get(v_a_1311_, 0);
                    v_isSharedCheck_1540_ = (!crate::leanh::lean_is_exclusive(v_a_1311_)) as u8;
                    if v_isSharedCheck_1540_ == 0 {
                        v___x_1317_ = v_a_1311_;
                        v_isShared_1318_ = v_isSharedCheck_1540_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1315_);
                        crate::leanh::lean_dec(v_a_1311_);
                        v___x_1317_ = crate::leanh::lean_box(0);
                        v_isShared_1318_ = v_isSharedCheck_1540_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1311_);
                    crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                    crate::leanh::lean_dec(v_val_1309_);
                    crate::leanh::lean_del_object(v___x_1301_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v___x_1541_ = crate::leanh::lean_box(0);
                    if v_isShared_1314_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1541_);
                        v___x_1543_ = v___x_1313_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
                        v___x_1543_ = v_reuseFailAlloc_1544_;
                        state = 44;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_a_1305_);
                crate::leanh::lean_inc_ref(v_type_1282_);
                crate::leanh::lean_inc(v_val_1299_);
                v___x_1319_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(
                    v_val_1299_,
                    v_type_1282_,
                    v_a_1305_,
                    v_a_1287_,
                    v_a_1288_,
                    v_a_1289_,
                    v_a_1290_,
                    v_a_1291_,
                    v_a_1292_,
                );
                if crate::leanh::lean_obj_tag(v___x_1319_) == 0 {
                    v_a_1320_ = crate::leanh::lean_ctor_get(v___x_1319_, 0);
                    crate::leanh::lean_inc(v_a_1320_);
                    crate::leanh::lean_dec_ref_known(v___x_1319_, 1);
                    crate::leanh::lean_inc_ref(v_a_1305_);
                    crate::leanh::lean_inc_ref(v_type_1282_);
                    crate::leanh::lean_inc(v_val_1299_);
                    v___x_1321_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(
                        v_val_1299_,
                        v_type_1282_,
                        v_a_1305_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                        v_a_1292_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1321_) == 0 {
                        v_a_1322_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                        crate::leanh::lean_inc(v_a_1322_);
                        crate::leanh::lean_dec_ref_known(v___x_1321_, 1);
                        v___x_1323_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__3;
                        crate::leanh::lean_inc_ref(v_type_1282_);
                        crate::leanh::lean_inc(v_val_1299_);
                        v___x_1324_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getInst_x3f___redArg(v___x_1323_, v_val_1299_, v_type_1282_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                        if crate::leanh::lean_obj_tag(v___x_1324_) == 0 {
                            v_a_1325_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                            crate::leanh::lean_inc(v_a_1325_);
                            crate::leanh::lean_dec_ref_known(v___x_1324_, 1);
                            v___x_1326_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__5;
                            v___x_1327_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_val_1299_);
                            v___x_1328_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1328_, 0, v_val_1299_);
                            crate::leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                            crate::leanh::lean_inc_ref(v___x_1328_);
                            v___x_1329_ = l_Lean_mkConst(v___x_1326_, v___x_1328_);
                            crate::leanh::lean_inc(v_val_1309_);
                            crate::leanh::lean_inc_ref(v_type_1282_);
                            v___x_1330_ = l_Lean_mkAppB(v___x_1329_, v_type_1282_, v_val_1309_);
                            v___x_1331_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_1330_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                            if crate::leanh::lean_obj_tag(v___x_1331_) == 0 {
                                v_a_1332_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                                crate::leanh::lean_inc(v_a_1332_);
                                crate::leanh::lean_dec_ref_known(v___x_1331_, 1);
                                if crate::leanh::lean_obj_tag(v_a_1325_) == 1 {
                                    v_val_1386_ = crate::leanh::lean_ctor_get(v_a_1325_, 0);
                                    crate::leanh::lean_inc_ref(v_a_1325_);
                                    crate::leanh::lean_inc_ref(v_type_1282_);
                                    crate::leanh::lean_inc(v_val_1299_);
                                    v___x_1387_ =
                                        l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(
                                            v_val_1299_,
                                            v_type_1282_,
                                            v_a_1325_,
                                            v_a_1305_,
                                            v_a_1287_,
                                            v_a_1288_,
                                            v_a_1289_,
                                            v_a_1290_,
                                            v_a_1291_,
                                            v_a_1292_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_1387_) == 0 {
                                        v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                                        crate::leanh::lean_inc(v_a_1388_);
                                        crate::leanh::lean_dec_ref_known(v___x_1387_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_1388_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_1328_, 2);
                                            crate::leanh::lean_del_object(v___x_1301_);
                                            v_fst_1380_ = v_a_1388_;
                                            v_snd_1381_ = v_a_1388_;
                                            v___y_1382_ = v_a_1283_;
                                            v___y_1383_ = v_a_1291_;
                                            state = 14;
                                            continue;
                                        } else {
                                            v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__11;
                                            v___x_1390_ = l_Lean_mkConst(v___x_1389_, v___x_1328_);
                                            crate::leanh::lean_inc(v_val_1386_);
                                            crate::leanh::lean_inc_ref(v_type_1282_);
                                            v___x_1391_ = l_Lean_mkAppB(
                                                v___x_1390_,
                                                v_type_1282_,
                                                v_val_1386_,
                                            );
                                            v___x_1392_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_preprocess___redArg(v___x_1391_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                                            if crate::leanh::lean_obj_tag(v___x_1392_) == 0 {
                                                v_a_1393_ =
                                                    crate::leanh::lean_ctor_get(v___x_1392_, 0);
                                                crate::leanh::lean_inc(v_a_1393_);
                                                crate::leanh::lean_dec_ref_known(v___x_1392_, 1);
                                                crate::leanh::lean_inc_ref(v_type_1282_);
                                                v___x_1394_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                                                if crate::leanh::lean_obj_tag(v___x_1394_) == 0 {
                                                    v_a_1395_ =
                                                        crate::leanh::lean_ctor_get(v___x_1394_, 0);
                                                    crate::leanh::lean_inc(v_a_1395_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1394_,
                                                        1,
                                                    );
                                                    if v_isShared_1302_ == 0 {
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_1301_,
                                                            0,
                                                            v_a_1393_,
                                                        );
                                                        v___x_1397_ = v___x_1301_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_1490_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                1,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_1490_,
                                                            0,
                                                            v_a_1393_,
                                                        );
                                                        v___x_1397_ = v_reuseFailAlloc_1490_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_1393_);
                                                    crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                                                    crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                                                    crate::leanh::lean_dec(v_a_1332_);
                                                    crate::leanh::lean_dec(v_a_1322_);
                                                    crate::leanh::lean_dec(v_a_1320_);
                                                    crate::leanh::lean_del_object(v___x_1317_);
                                                    crate::leanh::lean_dec(v_val_1315_);
                                                    crate::leanh::lean_dec(v_val_1309_);
                                                    crate::leanh::lean_del_object(v___x_1301_);
                                                    crate::leanh::lean_dec(v_val_1299_);
                                                    crate::leanh::lean_dec_ref(v_type_1282_);
                                                    return v___x_1394_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                                                crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                                                crate::leanh::lean_dec(v_a_1332_);
                                                crate::leanh::lean_dec(v_a_1322_);
                                                crate::leanh::lean_dec(v_a_1320_);
                                                crate::leanh::lean_del_object(v___x_1317_);
                                                crate::leanh::lean_dec(v_val_1315_);
                                                crate::leanh::lean_dec(v_val_1309_);
                                                crate::leanh::lean_del_object(v___x_1301_);
                                                crate::leanh::lean_dec(v_val_1299_);
                                                crate::leanh::lean_dec_ref(v_type_1282_);
                                                v_a_1491_ =
                                                    crate::leanh::lean_ctor_get(v___x_1392_, 0);
                                                v_isSharedCheck_1498_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1392_))
                                                        as u8;
                                                if v_isSharedCheck_1498_ == 0 {
                                                    v___x_1493_ = v___x_1392_;
                                                    v_isShared_1494_ = v_isSharedCheck_1498_;
                                                    state = 32;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1491_);
                                                    crate::leanh::lean_dec(v___x_1392_);
                                                    v___x_1493_ = crate::leanh::lean_box(0);
                                                    v_isShared_1494_ = v_isSharedCheck_1498_;
                                                    state = 32;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                                        crate::leanh::lean_dec(v_a_1332_);
                                        crate::leanh::lean_dec_ref_known(v___x_1328_, 2);
                                        crate::leanh::lean_dec(v_a_1322_);
                                        crate::leanh::lean_dec(v_a_1320_);
                                        crate::leanh::lean_del_object(v___x_1317_);
                                        crate::leanh::lean_dec(v_val_1315_);
                                        crate::leanh::lean_dec(v_val_1309_);
                                        crate::leanh::lean_del_object(v___x_1301_);
                                        crate::leanh::lean_dec(v_val_1299_);
                                        crate::leanh::lean_dec_ref(v_type_1282_);
                                        v_a_1499_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                                        v_isSharedCheck_1506_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                                        if v_isSharedCheck_1506_ == 0 {
                                            v___x_1501_ = v___x_1387_;
                                            v_isShared_1502_ = v_isSharedCheck_1506_;
                                            state = 34;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1499_);
                                            crate::leanh::lean_dec(v___x_1387_);
                                            v___x_1501_ = crate::leanh::lean_box(0);
                                            v_isShared_1502_ = v_isSharedCheck_1506_;
                                            state = 34;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_1328_, 2);
                                    crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                                    crate::leanh::lean_del_object(v___x_1301_);
                                    v___x_1507_ = crate::leanh::lean_box(0);
                                    v_fst_1380_ = v___x_1507_;
                                    v_snd_1381_ = v___x_1507_;
                                    v___y_1382_ = v_a_1283_;
                                    v___y_1383_ = v_a_1291_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_1328_, 2);
                                crate::leanh::lean_dec(v_a_1325_);
                                crate::leanh::lean_dec(v_a_1322_);
                                crate::leanh::lean_dec(v_a_1320_);
                                crate::leanh::lean_del_object(v___x_1317_);
                                crate::leanh::lean_dec(v_val_1315_);
                                crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                                crate::leanh::lean_dec(v_val_1309_);
                                crate::leanh::lean_del_object(v___x_1301_);
                                crate::leanh::lean_dec(v_val_1299_);
                                crate::leanh::lean_dec_ref(v_type_1282_);
                                v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                                v_isSharedCheck_1515_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                                if v_isSharedCheck_1515_ == 0 {
                                    v___x_1510_ = v___x_1331_;
                                    v_isShared_1511_ = v_isSharedCheck_1515_;
                                    state = 36;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1508_);
                                    crate::leanh::lean_dec(v___x_1331_);
                                    v___x_1510_ = crate::leanh::lean_box(0);
                                    v_isShared_1511_ = v_isSharedCheck_1515_;
                                    state = 36;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1322_);
                            crate::leanh::lean_dec(v_a_1320_);
                            crate::leanh::lean_del_object(v___x_1317_);
                            crate::leanh::lean_dec(v_val_1315_);
                            crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                            crate::leanh::lean_dec(v_val_1309_);
                            crate::leanh::lean_del_object(v___x_1301_);
                            crate::leanh::lean_dec(v_val_1299_);
                            crate::leanh::lean_dec_ref(v_type_1282_);
                            v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                            v_isSharedCheck_1523_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1324_)) as u8;
                            if v_isSharedCheck_1523_ == 0 {
                                v___x_1518_ = v___x_1324_;
                                v_isShared_1519_ = v_isSharedCheck_1523_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1516_);
                                crate::leanh::lean_dec(v___x_1324_);
                                v___x_1518_ = crate::leanh::lean_box(0);
                                v_isShared_1519_ = v_isSharedCheck_1523_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1320_);
                        crate::leanh::lean_del_object(v___x_1317_);
                        crate::leanh::lean_dec(v_val_1315_);
                        crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                        crate::leanh::lean_dec(v_val_1309_);
                        crate::leanh::lean_del_object(v___x_1301_);
                        crate::leanh::lean_dec(v_val_1299_);
                        crate::leanh::lean_dec_ref(v_type_1282_);
                        v_a_1524_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                        v_isSharedCheck_1531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1321_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1321_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1524_);
                            crate::leanh::lean_dec(v___x_1321_);
                            v___x_1526_ = crate::leanh::lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1317_);
                    crate::leanh::lean_dec(v_val_1315_);
                    crate::leanh::lean_dec_ref_known(v_a_1305_, 1);
                    crate::leanh::lean_dec(v_val_1309_);
                    crate::leanh::lean_del_object(v___x_1301_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1319_, 0);
                    v_isSharedCheck_1539_ = (!crate::leanh::lean_is_exclusive(v___x_1319_)) as u8;
                    if v_isSharedCheck_1539_ == 0 {
                        v___x_1534_ = v___x_1319_;
                        v_isShared_1535_ = v_isSharedCheck_1539_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1532_);
                        crate::leanh::lean_dec(v___x_1319_);
                        v___x_1534_ = crate::leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1539_;
                        state = 42;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1342_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1340_, v___y_1341_);
                if crate::leanh::lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = crate::leanh::lean_ctor_get(v___x_1342_, 0);
                    crate::leanh::lean_inc(v_a_1343_);
                    crate::leanh::lean_dec_ref_known(v___x_1342_, 1);
                    v_structs_1344_ = crate::leanh::lean_ctor_get(v_a_1343_, 0);
                    crate::leanh::lean_inc_ref(v_structs_1344_);
                    crate::leanh::lean_dec(v_a_1343_);
                    v___x_1345_ = lean_array_get_size(v_structs_1344_);
                    crate::leanh::lean_dec_ref(v_structs_1344_);
                    v___x_1346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__7);
                    v___x_1347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___closed__9);
                    v___x_1348_ = crate::leanh::lean_alloc_ctor(0, 22, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1345_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 1, v_type_1282_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 2, v_val_1299_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 3, v_val_1315_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 4, v_val_1309_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 5, v_a_1325_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 6, v_a_1320_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 7, v_a_1322_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 8, v___y_1335_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 9, v_fst_1336_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 10, v_fst_1337_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 11, v_fst_1338_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 12, v_a_1332_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 13, v___y_1334_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 14, v___x_1346_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 15, v___x_1347_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 16, v___x_1347_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 17, v___x_1347_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 18, v___x_1346_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 19, v___x_1346_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 20, v___x_1346_);
                    crate::leanh::lean_ctor_set(v___x_1348_, 21, v___x_1327_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1348_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 22) as u32,
                        v_snd_1339_,
                    );
                    v___f_1349_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_1349_, 0, v___x_1348_);
                    v___x_1350_ = l_Lean_Meta_Grind_Order_orderExt;
                    v___x_1351_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1350_, v___f_1349_, v___y_1340_);
                    if crate::leanh::lean_obj_tag(v___x_1351_) == 0 {
                        v_isSharedCheck_1361_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1361_ == 0 {
                            v_unused_1362_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
                            crate::leanh::lean_dec(v_unused_1362_);
                            v___x_1353_ = v___x_1351_;
                            v_isShared_1354_ = v_isSharedCheck_1361_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1351_);
                            v___x_1353_ = crate::leanh::lean_box(0);
                            v_isShared_1354_ = v_isSharedCheck_1361_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1317_);
                        v_a_1363_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
                        v_isSharedCheck_1370_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1351_)) as u8;
                        if v_isSharedCheck_1370_ == 0 {
                            v___x_1365_ = v___x_1351_;
                            v_isShared_1366_ = v_isSharedCheck_1370_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1363_);
                            crate::leanh::lean_dec(v___x_1351_);
                            v___x_1365_ = crate::leanh::lean_box(0);
                            v_isShared_1366_ = v_isSharedCheck_1370_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1338_);
                    crate::leanh::lean_dec(v_fst_1337_);
                    crate::leanh::lean_dec(v_fst_1336_);
                    crate::leanh::lean_dec(v___y_1335_);
                    crate::leanh::lean_dec(v___y_1334_);
                    crate::leanh::lean_dec(v_a_1332_);
                    crate::leanh::lean_dec(v_a_1325_);
                    crate::leanh::lean_dec(v_a_1322_);
                    crate::leanh::lean_dec(v_a_1320_);
                    crate::leanh::lean_del_object(v___x_1317_);
                    crate::leanh::lean_dec(v_val_1315_);
                    crate::leanh::lean_dec(v_val_1309_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1342_, 0);
                    v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v___x_1342_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v___x_1373_ = v___x_1342_;
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1371_);
                        crate::leanh::lean_dec(v___x_1342_);
                        v___x_1373_ = crate::leanh::lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1345_);
                    v___x_1356_ = v___x_1317_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1345_);
                    v___x_1356_ = v_reuseFailAlloc_1360_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1353_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1353_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1359_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1358_;
            }
            10 => {
                if v_isShared_1366_ == 0 {
                    v___x_1368_ = v___x_1365_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
                    v___x_1368_ = v_reuseFailAlloc_1369_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1368_;
            }
            12 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1376_;
            }
            14 => {
                v___x_1384_ = crate::leanh::lean_box(0);
                v___x_1385_ = 0;
                crate::leanh::lean_inc_n(v_fst_1380_, 2);
                v___y_1334_ = v_snd_1381_;
                v___y_1335_ = v_fst_1380_;
                v_fst_1336_ = v___x_1384_;
                v_fst_1337_ = v_fst_1380_;
                v_fst_1338_ = v_fst_1380_;
                v_snd_1339_ = v___x_1385_;
                v___y_1340_ = v___y_1382_;
                v___y_1341_ = v___y_1383_;
                state = 6;
                continue;
            }
            15 => {
                v___x_1398_ = 0;
                v___x_1399_ = 1;
                if crate::leanh::lean_obj_tag(v_a_1395_) == 1 {
                    v_val_1400_ = crate::leanh::lean_ctor_get(v_a_1395_, 0);
                    crate::leanh::lean_inc(v_val_1400_);
                    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v_val_1400_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1398_,
                    );
                    v___x_1402_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                        v___x_1401_,
                        v_a_1283_,
                        v_a_1284_,
                        v_a_1285_,
                        v_a_1286_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                        v_a_1292_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1402_) == 0 {
                        v_a_1403_ = crate::leanh::lean_ctor_get(v___x_1402_, 0);
                        crate::leanh::lean_inc(v_a_1403_);
                        crate::leanh::lean_dec_ref_known(v___x_1402_, 1);
                        v___x_1404_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_1403_, v___x_1401_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                        crate::leanh::lean_dec(v_a_1403_);
                        v_a_1405_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                        crate::leanh::lean_inc(v_a_1405_);
                        crate::leanh::lean_dec_ref(v___x_1404_);
                        v___x_1406_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                            v___x_1401_,
                            v_a_1283_,
                            v_a_1284_,
                            v_a_1285_,
                            v_a_1286_,
                            v_a_1287_,
                            v_a_1288_,
                            v_a_1289_,
                            v_a_1290_,
                            v_a_1291_,
                            v_a_1292_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1406_) == 0 {
                            v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1406_, 0);
                            crate::leanh::lean_inc(v_a_1407_);
                            crate::leanh::lean_dec_ref_known(v___x_1406_, 1);
                            v___x_1408_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___lam__1(v_a_1407_, v___x_1401_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                            crate::leanh::lean_dec_ref_known(v___x_1401_, 1);
                            crate::leanh::lean_dec(v_a_1407_);
                            v_a_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                            v_isSharedCheck_1429_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                            if v_isSharedCheck_1429_ == 0 {
                                v___x_1411_ = v___x_1408_;
                                v_isShared_1412_ = v_isSharedCheck_1429_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1409_);
                                crate::leanh::lean_dec(v___x_1408_);
                                v___x_1411_ = crate::leanh::lean_box(0);
                                v_isShared_1412_ = v_isSharedCheck_1429_;
                                state = 16;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1405_);
                            crate::leanh::lean_dec_ref_known(v___x_1401_, 1);
                            crate::leanh::lean_dec_ref_known(v_a_1395_, 1);
                            crate::leanh::lean_dec_ref(v___x_1397_);
                            crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                            crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                            crate::leanh::lean_dec(v_a_1332_);
                            crate::leanh::lean_dec(v_a_1322_);
                            crate::leanh::lean_dec(v_a_1320_);
                            crate::leanh::lean_del_object(v___x_1317_);
                            crate::leanh::lean_dec(v_val_1315_);
                            crate::leanh::lean_dec(v_val_1309_);
                            crate::leanh::lean_dec(v_val_1299_);
                            crate::leanh::lean_dec_ref(v_type_1282_);
                            v_a_1430_ = crate::leanh::lean_ctor_get(v___x_1406_, 0);
                            v_isSharedCheck_1437_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1406_)) as u8;
                            if v_isSharedCheck_1437_ == 0 {
                                v___x_1432_ = v___x_1406_;
                                v_isShared_1433_ = v_isSharedCheck_1437_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1430_);
                                crate::leanh::lean_dec(v___x_1406_);
                                v___x_1432_ = crate::leanh::lean_box(0);
                                v_isShared_1433_ = v_isSharedCheck_1437_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1401_, 1);
                        crate::leanh::lean_dec_ref_known(v_a_1395_, 1);
                        crate::leanh::lean_dec_ref(v___x_1397_);
                        crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                        crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                        crate::leanh::lean_dec(v_a_1332_);
                        crate::leanh::lean_dec(v_a_1322_);
                        crate::leanh::lean_dec(v_a_1320_);
                        crate::leanh::lean_del_object(v___x_1317_);
                        crate::leanh::lean_dec(v_val_1315_);
                        crate::leanh::lean_dec(v_val_1309_);
                        crate::leanh::lean_dec(v_val_1299_);
                        crate::leanh::lean_dec_ref(v_type_1282_);
                        v_a_1438_ = crate::leanh::lean_ctor_get(v___x_1402_, 0);
                        v_isSharedCheck_1445_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1402_)) as u8;
                        if v_isSharedCheck_1445_ == 0 {
                            v___x_1440_ = v___x_1402_;
                            v_isShared_1441_ = v_isSharedCheck_1445_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1438_);
                            crate::leanh::lean_dec(v___x_1402_);
                            v___x_1440_ = crate::leanh::lean_box(0);
                            v_isShared_1441_ = v_isSharedCheck_1445_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1395_);
                    crate::leanh::lean_inc_ref(v_type_1282_);
                    v___x_1446_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(
                        v_type_1282_,
                        v_a_1283_,
                        v_a_1284_,
                        v_a_1285_,
                        v_a_1286_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                        v_a_1292_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1446_) == 0 {
                        v_a_1447_ = crate::leanh::lean_ctor_get(v___x_1446_, 0);
                        v_isSharedCheck_1489_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1446_)) as u8;
                        if v_isSharedCheck_1489_ == 0 {
                            v___x_1449_ = v___x_1446_;
                            v_isShared_1450_ = v_isSharedCheck_1489_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1447_);
                            crate::leanh::lean_dec(v___x_1446_);
                            v___x_1449_ = crate::leanh::lean_box(0);
                            v_isShared_1450_ = v_isSharedCheck_1489_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1397_);
                        crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                        crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                        crate::leanh::lean_dec(v_a_1332_);
                        crate::leanh::lean_dec(v_a_1322_);
                        crate::leanh::lean_dec(v_a_1320_);
                        crate::leanh::lean_del_object(v___x_1317_);
                        crate::leanh::lean_dec(v_val_1315_);
                        crate::leanh::lean_dec(v_val_1309_);
                        crate::leanh::lean_dec(v_val_1299_);
                        crate::leanh::lean_dec_ref(v_type_1282_);
                        return v___x_1446_;
                    }
                }
            }
            16 => {
                v_ringInst_1413_ = crate::leanh::lean_ctor_get(v_a_1405_, 3);
                crate::leanh::lean_inc_ref(v_ringInst_1413_);
                crate::leanh::lean_dec(v_a_1405_);
                v_semiringInst_1414_ = crate::leanh::lean_ctor_get(v_a_1409_, 4);
                crate::leanh::lean_inc_ref(v_semiringInst_1414_);
                crate::leanh::lean_dec(v_a_1409_);
                crate::leanh::lean_inc(v_val_1315_);
                crate::leanh::lean_inc(v_val_1386_);
                crate::leanh::lean_inc(v_val_1309_);
                crate::leanh::lean_inc_ref(v_type_1282_);
                crate::leanh::lean_inc(v_val_1299_);
                v___x_1415_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_1299_, v_type_1282_, v_semiringInst_1414_, v_val_1309_, v_val_1386_, v_val_1315_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                if crate::leanh::lean_obj_tag(v___x_1415_) == 0 {
                    v_a_1416_ = crate::leanh::lean_ctor_get(v___x_1415_, 0);
                    crate::leanh::lean_inc(v_a_1416_);
                    crate::leanh::lean_dec_ref_known(v___x_1415_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1416_) == 1 {
                        if v_isShared_1412_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1411_, 1);
                            crate::leanh::lean_ctor_set(v___x_1411_, 0, v_ringInst_1413_);
                            v___x_1418_ = v___x_1411_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_1419_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1419_,
                                0,
                                v_ringInst_1413_,
                            );
                            v___x_1418_ = v_reuseFailAlloc_1419_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1416_);
                        crate::leanh::lean_dec_ref(v_ringInst_1413_);
                        crate::leanh::lean_del_object(v___x_1411_);
                        crate::leanh::lean_dec_ref_known(v_a_1395_, 1);
                        v___x_1420_ = crate::leanh::lean_box(0);
                        v___y_1334_ = v___x_1397_;
                        v___y_1335_ = v_a_1388_;
                        v_fst_1336_ = v___x_1420_;
                        v_fst_1337_ = v___x_1420_;
                        v_fst_1338_ = v___x_1420_;
                        v_snd_1339_ = v___x_1399_;
                        v___y_1340_ = v_a_1283_;
                        v___y_1341_ = v_a_1291_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ringInst_1413_);
                    crate::leanh::lean_del_object(v___x_1411_);
                    crate::leanh::lean_dec_ref_known(v_a_1395_, 1);
                    crate::leanh::lean_dec_ref(v___x_1397_);
                    crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                    crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                    crate::leanh::lean_dec(v_a_1332_);
                    crate::leanh::lean_dec(v_a_1322_);
                    crate::leanh::lean_dec(v_a_1320_);
                    crate::leanh::lean_del_object(v___x_1317_);
                    crate::leanh::lean_dec(v_val_1315_);
                    crate::leanh::lean_dec(v_val_1309_);
                    crate::leanh::lean_dec(v_val_1299_);
                    crate::leanh::lean_dec_ref(v_type_1282_);
                    v_a_1421_ = crate::leanh::lean_ctor_get(v___x_1415_, 0);
                    v_isSharedCheck_1428_ = (!crate::leanh::lean_is_exclusive(v___x_1415_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1415_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1421_);
                        crate::leanh::lean_dec(v___x_1415_);
                        v___x_1423_ = crate::leanh::lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                v___y_1334_ = v___x_1397_;
                v___y_1335_ = v_a_1388_;
                v_fst_1336_ = v_a_1395_;
                v_fst_1337_ = v___x_1418_;
                v_fst_1338_ = v_a_1416_;
                v_snd_1339_ = v___x_1399_;
                v___y_1340_ = v_a_1283_;
                v___y_1341_ = v_a_1291_;
                state = 6;
                continue;
            }
            18 => {
                if v_isShared_1424_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
                    v___x_1426_ = v_reuseFailAlloc_1427_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1426_;
            }
            20 => {
                if v_isShared_1433_ == 0 {
                    v___x_1435_ = v___x_1432_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
                    v___x_1435_ = v_reuseFailAlloc_1436_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1435_;
            }
            22 => {
                if v_isShared_1441_ == 0 {
                    v___x_1443_ = v___x_1440_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
                    v___x_1443_ = v_reuseFailAlloc_1444_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1443_;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v_a_1447_) == 1 {
                    v_val_1451_ = crate::leanh::lean_ctor_get(v_a_1447_, 0);
                    v___x_1452_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
                        v_val_1451_,
                        v_a_1283_,
                        v_a_1284_,
                        v_a_1285_,
                        v_a_1286_,
                        v_a_1287_,
                        v_a_1288_,
                        v_a_1289_,
                        v_a_1290_,
                        v_a_1291_,
                        v_a_1292_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1452_) == 0 {
                        v_a_1453_ = crate::leanh::lean_ctor_get(v___x_1452_, 0);
                        crate::leanh::lean_inc(v_a_1453_);
                        crate::leanh::lean_dec_ref_known(v___x_1452_, 1);
                        v___x_1454_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
                            v_val_1451_,
                            v_a_1283_,
                            v_a_1284_,
                            v_a_1285_,
                            v_a_1286_,
                            v_a_1287_,
                            v_a_1288_,
                            v_a_1289_,
                            v_a_1290_,
                            v_a_1291_,
                            v_a_1292_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                            v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                            crate::leanh::lean_inc(v_a_1455_);
                            crate::leanh::lean_dec_ref_known(v___x_1454_, 1);
                            v_semiringInst_1456_ = crate::leanh::lean_ctor_get(v_a_1453_, 4);
                            crate::leanh::lean_inc_ref(v_semiringInst_1456_);
                            crate::leanh::lean_dec(v_a_1453_);
                            v_ringInst_1457_ = crate::leanh::lean_ctor_get(v_a_1455_, 3);
                            crate::leanh::lean_inc_ref(v_ringInst_1457_);
                            crate::leanh::lean_dec(v_a_1455_);
                            crate::leanh::lean_inc(v_val_1315_);
                            crate::leanh::lean_inc(v_val_1386_);
                            crate::leanh::lean_inc(v_val_1309_);
                            crate::leanh::lean_inc_ref(v_type_1282_);
                            crate::leanh::lean_inc(v_val_1299_);
                            v___x_1458_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_mkOrderedRingInst_x3f___redArg(v_val_1299_, v_type_1282_, v_semiringInst_1456_, v_val_1309_, v_val_1386_, v_val_1315_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
                            if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                                v_a_1459_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                                crate::leanh::lean_inc(v_a_1459_);
                                crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
                                if crate::leanh::lean_obj_tag(v_a_1459_) == 1 {
                                    if v_isShared_1450_ == 0 {
                                        crate::leanh::lean_ctor_set_tag(v___x_1449_, 1);
                                        crate::leanh::lean_ctor_set(
                                            v___x_1449_,
                                            0,
                                            v_ringInst_1457_,
                                        );
                                        v___x_1461_ = v___x_1449_;
                                        state = 25;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1462_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1462_,
                                            0,
                                            v_ringInst_1457_,
                                        );
                                        v___x_1461_ = v_reuseFailAlloc_1462_;
                                        state = 25;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1459_);
                                    crate::leanh::lean_dec_ref(v_ringInst_1457_);
                                    crate::leanh::lean_dec_ref_known(v_a_1447_, 1);
                                    crate::leanh::lean_del_object(v___x_1449_);
                                    v___x_1463_ = crate::leanh::lean_box(0);
                                    v___y_1334_ = v___x_1397_;
                                    v___y_1335_ = v_a_1388_;
                                    v_fst_1336_ = v___x_1463_;
                                    v_fst_1337_ = v___x_1463_;
                                    v_fst_1338_ = v___x_1463_;
                                    v_snd_1339_ = v___x_1399_;
                                    v___y_1340_ = v_a_1283_;
                                    v___y_1341_ = v_a_1291_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_ringInst_1457_);
                                crate::leanh::lean_dec_ref_known(v_a_1447_, 1);
                                crate::leanh::lean_del_object(v___x_1449_);
                                crate::leanh::lean_dec_ref(v___x_1397_);
                                crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                                crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                                crate::leanh::lean_dec(v_a_1332_);
                                crate::leanh::lean_dec(v_a_1322_);
                                crate::leanh::lean_dec(v_a_1320_);
                                crate::leanh::lean_del_object(v___x_1317_);
                                crate::leanh::lean_dec(v_val_1315_);
                                crate::leanh::lean_dec(v_val_1309_);
                                crate::leanh::lean_dec(v_val_1299_);
                                crate::leanh::lean_dec_ref(v_type_1282_);
                                v_a_1464_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                                v_isSharedCheck_1471_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1458_)) as u8;
                                if v_isSharedCheck_1471_ == 0 {
                                    v___x_1466_ = v___x_1458_;
                                    v_isShared_1467_ = v_isSharedCheck_1471_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1464_);
                                    crate::leanh::lean_dec(v___x_1458_);
                                    v___x_1466_ = crate::leanh::lean_box(0);
                                    v_isShared_1467_ = v_isSharedCheck_1471_;
                                    state = 26;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1453_);
                            crate::leanh::lean_dec_ref_known(v_a_1447_, 1);
                            crate::leanh::lean_del_object(v___x_1449_);
                            crate::leanh::lean_dec_ref(v___x_1397_);
                            crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                            crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                            crate::leanh::lean_dec(v_a_1332_);
                            crate::leanh::lean_dec(v_a_1322_);
                            crate::leanh::lean_dec(v_a_1320_);
                            crate::leanh::lean_del_object(v___x_1317_);
                            crate::leanh::lean_dec(v_val_1315_);
                            crate::leanh::lean_dec(v_val_1309_);
                            crate::leanh::lean_dec(v_val_1299_);
                            crate::leanh::lean_dec_ref(v_type_1282_);
                            v_a_1472_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                            v_isSharedCheck_1479_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                            if v_isSharedCheck_1479_ == 0 {
                                v___x_1474_ = v___x_1454_;
                                v_isShared_1475_ = v_isSharedCheck_1479_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1472_);
                                crate::leanh::lean_dec(v___x_1454_);
                                v___x_1474_ = crate::leanh::lean_box(0);
                                v_isShared_1475_ = v_isSharedCheck_1479_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1447_, 1);
                        crate::leanh::lean_del_object(v___x_1449_);
                        crate::leanh::lean_dec_ref(v___x_1397_);
                        crate::leanh::lean_dec_ref_known(v_a_1388_, 1);
                        crate::leanh::lean_dec_ref_known(v_a_1325_, 1);
                        crate::leanh::lean_dec(v_a_1332_);
                        crate::leanh::lean_dec(v_a_1322_);
                        crate::leanh::lean_dec(v_a_1320_);
                        crate::leanh::lean_del_object(v___x_1317_);
                        crate::leanh::lean_dec(v_val_1315_);
                        crate::leanh::lean_dec(v_val_1309_);
                        crate::leanh::lean_dec(v_val_1299_);
                        crate::leanh::lean_dec_ref(v_type_1282_);
                        v_a_1480_ = crate::leanh::lean_ctor_get(v___x_1452_, 0);
                        v_isSharedCheck_1487_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1452_)) as u8;
                        if v_isSharedCheck_1487_ == 0 {
                            v___x_1482_ = v___x_1452_;
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1480_);
                            crate::leanh::lean_dec(v___x_1452_);
                            v___x_1482_ = crate::leanh::lean_box(0);
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1449_);
                    crate::leanh::lean_dec(v_a_1447_);
                    v___x_1488_ = crate::leanh::lean_box(0);
                    v___y_1334_ = v___x_1397_;
                    v___y_1335_ = v_a_1388_;
                    v_fst_1336_ = v___x_1488_;
                    v_fst_1337_ = v___x_1488_;
                    v_fst_1338_ = v___x_1488_;
                    v_snd_1339_ = v___x_1398_;
                    v___y_1340_ = v_a_1283_;
                    v___y_1341_ = v_a_1291_;
                    state = 6;
                    continue;
                }
            }
            25 => {
                v___y_1334_ = v___x_1397_;
                v___y_1335_ = v_a_1388_;
                v_fst_1336_ = v_a_1447_;
                v_fst_1337_ = v___x_1461_;
                v_fst_1338_ = v_a_1459_;
                v_snd_1339_ = v___x_1398_;
                v___y_1340_ = v_a_1283_;
                v___y_1341_ = v_a_1291_;
                state = 6;
                continue;
            }
            26 => {
                if v_isShared_1467_ == 0 {
                    v___x_1469_ = v___x_1466_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1469_;
            }
            28 => {
                if v_isShared_1475_ == 0 {
                    v___x_1477_ = v___x_1474_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1477_;
            }
            30 => {
                if v_isShared_1483_ == 0 {
                    v___x_1485_ = v___x_1482_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
                    v___x_1485_ = v_reuseFailAlloc_1486_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1485_;
            }
            32 => {
                if v_isShared_1494_ == 0 {
                    v___x_1496_ = v___x_1493_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1496_;
            }
            34 => {
                if v_isShared_1502_ == 0 {
                    v___x_1504_ = v___x_1501_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1504_;
            }
            36 => {
                if v_isShared_1511_ == 0 {
                    v___x_1513_ = v___x_1510_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1513_;
            }
            38 => {
                if v_isShared_1519_ == 0 {
                    v___x_1521_ = v___x_1518_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
                    v___x_1521_ = v_reuseFailAlloc_1522_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1521_;
            }
            40 => {
                if v_isShared_1527_ == 0 {
                    v___x_1529_ = v___x_1526_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1529_;
            }
            42 => {
                if v_isShared_1535_ == 0 {
                    v___x_1537_ = v___x_1534_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
                    v___x_1537_ = v_reuseFailAlloc_1538_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_1537_;
            }
            44 => {
                return v___x_1543_;
            }
            45 => {
                if v_isShared_1549_ == 0 {
                    v___x_1551_ = v___x_1548_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
                    v___x_1551_ = v_reuseFailAlloc_1552_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_1551_;
            }
            47 => {
                return v___x_1556_;
            }
            48 => {
                if v_isShared_1562_ == 0 {
                    v___x_1564_ = v___x_1561_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
                    v___x_1564_ = v_reuseFailAlloc_1565_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_1564_;
            }
            50 => {
                return v___x_1570_;
            }
            51 => {
                if v_isShared_1576_ == 0 {
                    v___x_1578_ = v___x_1575_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
                    v___x_1578_ = v_reuseFailAlloc_1579_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_1578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f___boxed(
    mut v_type_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
    mut v_a_1587_: *mut crate::leanh::LeanObject,
    mut v_a_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1593_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
    crate::leanh::lean_dec(v_a_1591_);
    crate::leanh::lean_dec_ref(v_a_1590_);
    crate::leanh::lean_dec(v_a_1589_);
    crate::leanh::lean_dec_ref(v_a_1588_);
    crate::leanh::lean_dec(v_a_1587_);
    crate::leanh::lean_dec_ref(v_a_1586_);
    crate::leanh::lean_dec(v_a_1585_);
    crate::leanh::lean_dec_ref(v_a_1584_);
    crate::leanh::lean_dec(v_a_1583_);
    crate::leanh::lean_dec(v_a_1582_);
    return v_res_1593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_1594_: *mut crate::leanh::LeanObject,
    mut v_x_1595_: *mut crate::leanh::LeanObject,
    mut v_x_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1598_ = crate::leanh::lean_ctor_get(v_x_1594_, 0);
                v_vs_1599_ = crate::leanh::lean_ctor_get(v_x_1594_, 1);
                v_isSharedCheck_1623_ = (!crate::leanh::lean_is_exclusive(v_x_1594_)) as u8;
                if v_isSharedCheck_1623_ == 0 {
                    v___x_1601_ = v_x_1594_;
                    v_isShared_1602_ = v_isSharedCheck_1623_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1599_);
                    crate::leanh::lean_inc(v_ks_1598_);
                    crate::leanh::lean_dec(v_x_1594_);
                    v___x_1601_ = crate::leanh::lean_box(0);
                    v_isShared_1602_ = v_isSharedCheck_1623_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1603_ = lean_array_get_size(v_ks_1598_);
                v___x_1604_ = lean_nat_dec_lt(v_x_1595_, v___x_1603_);
                if v___x_1604_ == 0 {
                    crate::leanh::lean_dec(v_x_1595_);
                    v___x_1605_ = lean_array_push(v_ks_1598_, v_x_1596_);
                    v___x_1606_ = lean_array_push(v_vs_1599_, v_x_1597_);
                    if v_isShared_1602_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1601_, 1, v___x_1606_);
                        crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1605_);
                        v___x_1608_ = v___x_1601_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1609_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1605_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1606_);
                        v___x_1608_ = v_reuseFailAlloc_1609_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1610_ = lean_array_fget_borrowed(v_ks_1598_, v_x_1595_);
                    v___x_1611_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1596_,
                            v_k_x27_1610_,
                        );
                    if v___x_1611_ == 0 {
                        if v_isShared_1602_ == 0 {
                            v___x_1613_ = v___x_1601_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1617_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_ks_1598_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_vs_1599_);
                            v___x_1613_ = v_reuseFailAlloc_1617_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1618_ = lean_array_fset(v_ks_1598_, v_x_1595_, v_x_1596_);
                        v___x_1619_ = lean_array_fset(v_vs_1599_, v_x_1595_, v_x_1597_);
                        crate::leanh::lean_dec(v_x_1595_);
                        if v_isShared_1602_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1601_, 1, v___x_1619_);
                            crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1618_);
                            v___x_1621_ = v___x_1601_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1622_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1618_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
                            v___x_1621_ = v_reuseFailAlloc_1622_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1608_;
            }
            3 => {
                v___x_1614_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1615_ = lean_nat_add(v_x_1595_, v___x_1614_);
                crate::leanh::lean_dec(v_x_1595_);
                v_x_1594_ = v___x_1613_;
                v_x_1595_ = v___x_1615_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_1624_: *mut crate::leanh::LeanObject,
    mut v_k_1625_: *mut crate::leanh::LeanObject,
    mut v_v_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1628_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1624_, v___x_1627_, v_k_1625_, v_v_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1629_: usize = 0;
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: usize = 0;
    v___x_1629_ = 5usize;
    v___x_1630_ = 1usize;
    v___x_1631_ = lean_usize_shift_left(v___x_1630_, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: usize = 0;
    v___x_1632_ = 1usize;
    v___x_1633_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_1634_ = lean_usize_sub(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1635_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(
    mut v_x_1636_: *mut crate::leanh::LeanObject,
    mut v_x_1637_: usize,
    mut v_x_1638_: usize,
    mut v_x_1639_: *mut crate::leanh::LeanObject,
    mut v_x_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: usize = 0;
    let mut v_j_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v_v_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1672_: u8 = 0;
    let mut v_node_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1677_: usize = 0;
    let mut v___x_1678_: usize = 0;
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_unused_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: u8 = 0;
    let mut v_ks_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: usize = 0;
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1636_) == 0 {
                    v_es_1641_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                    v___x_1642_ = 5usize;
                    v___x_1643_ = 1usize;
                    v___x_1644_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_1645_ = lean_usize_land(v_x_1637_, v___x_1644_);
                    v_j_1646_ = lean_usize_to_nat(v___x_1645_);
                    v___x_1647_ = lean_array_get_size(v_es_1641_);
                    v___x_1648_ = lean_nat_dec_lt(v_j_1646_, v___x_1647_);
                    if v___x_1648_ == 0 {
                        crate::leanh::lean_dec(v_j_1646_);
                        crate::leanh::lean_dec(v_x_1640_);
                        crate::leanh::lean_dec_ref(v_x_1639_);
                        return v_x_1636_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1641_);
                        v_isSharedCheck_1685_ = (!crate::leanh::lean_is_exclusive(v_x_1636_)) as u8;
                        if v_isSharedCheck_1685_ == 0 {
                            v_unused_1686_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                            crate::leanh::lean_dec(v_unused_1686_);
                            v___x_1650_ = v_x_1636_;
                            v_isShared_1651_ = v_isSharedCheck_1685_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1636_);
                            v___x_1650_ = crate::leanh::lean_box(0);
                            v_isShared_1651_ = v_isSharedCheck_1685_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1687_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                    v_vs_1688_ = crate::leanh::lean_ctor_get(v_x_1636_, 1);
                    v_isSharedCheck_1708_ = (!crate::leanh::lean_is_exclusive(v_x_1636_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1690_ = v_x_1636_;
                        v_isShared_1691_ = v_isSharedCheck_1708_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1688_);
                        crate::leanh::lean_inc(v_ks_1687_);
                        crate::leanh::lean_dec(v_x_1636_);
                        v___x_1690_ = crate::leanh::lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1708_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1652_ = lean_array_fget(v_es_1641_, v_j_1646_);
                v___x_1653_ = crate::leanh::lean_box(0);
                v_xs_x27_1654_ = lean_array_fset(v_es_1641_, v_j_1646_, v___x_1653_);
                match crate::leanh::lean_obj_tag(v_v_1652_) {
                    0 => {
                        v_key_1661_ = crate::leanh::lean_ctor_get(v_v_1652_, 0);
                        v_val_1662_ = crate::leanh::lean_ctor_get(v_v_1652_, 1);
                        v_isSharedCheck_1672_ = (!crate::leanh::lean_is_exclusive(v_v_1652_)) as u8;
                        if v_isSharedCheck_1672_ == 0 {
                            v___x_1664_ = v_v_1652_;
                            v_isShared_1665_ = v_isSharedCheck_1672_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1662_);
                            crate::leanh::lean_inc(v_key_1661_);
                            crate::leanh::lean_dec(v_v_1652_);
                            v___x_1664_ = crate::leanh::lean_box(0);
                            v_isShared_1665_ = v_isSharedCheck_1672_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1673_ = crate::leanh::lean_ctor_get(v_v_1652_, 0);
                        v_isSharedCheck_1683_ = (!crate::leanh::lean_is_exclusive(v_v_1652_)) as u8;
                        if v_isSharedCheck_1683_ == 0 {
                            v___x_1675_ = v_v_1652_;
                            v_isShared_1676_ = v_isSharedCheck_1683_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1673_);
                            crate::leanh::lean_dec(v_v_1652_);
                            v___x_1675_ = crate::leanh::lean_box(0);
                            v_isShared_1676_ = v_isSharedCheck_1683_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1684_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1684_, 0, v_x_1639_);
                        crate::leanh::lean_ctor_set(v___x_1684_, 1, v_x_1640_);
                        v___y_1656_ = v___x_1684_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1657_ = lean_array_fset(v_xs_x27_1654_, v_j_1646_, v___y_1656_);
                crate::leanh::lean_dec(v_j_1646_);
                if v_isShared_1651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1657_);
                    v___x_1659_ = v___x_1650_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1659_;
            }
            4 => {
                v___x_1666_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1639_,
                        v_key_1661_,
                    );
                if v___x_1666_ == 0 {
                    crate::leanh::lean_del_object(v___x_1664_);
                    v___x_1667_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1661_,
                        v_val_1662_,
                        v_x_1639_,
                        v_x_1640_,
                    );
                    v___x_1668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1668_, 0, v___x_1667_);
                    v___y_1656_ = v___x_1668_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1662_);
                    crate::leanh::lean_dec(v_key_1661_);
                    if v_isShared_1665_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1664_, 1, v_x_1640_);
                        crate::leanh::lean_ctor_set(v___x_1664_, 0, v_x_1639_);
                        v___x_1670_ = v___x_1664_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_x_1639_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_x_1640_);
                        v___x_1670_ = v_reuseFailAlloc_1671_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1656_ = v___x_1670_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1677_ = lean_usize_shift_right(v_x_1637_, v___x_1642_);
                v___x_1678_ = lean_usize_add(v_x_1638_, v___x_1643_);
                v___x_1679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_node_1673_, v___x_1677_, v___x_1678_, v_x_1639_, v_x_1640_);
                if v_isShared_1676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1675_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1656_ = v___x_1681_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1691_ == 0 {
                    v___x_1693_ = v___x_1690_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_ks_1687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_vs_1688_);
                    v___x_1693_ = v_reuseFailAlloc_1707_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1694_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v___x_1693_, v_x_1639_, v_x_1640_);
                v___x_1702_ = 7usize;
                v___x_1703_ = lean_usize_dec_le(v___x_1702_, v_x_1638_);
                if v___x_1703_ == 0 {
                    v___x_1704_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1694_);
                    v___x_1705_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1706_ = lean_nat_dec_lt(v___x_1704_, v___x_1705_);
                    crate::leanh::lean_dec(v___x_1704_);
                    v___y_1696_ = v___x_1706_;
                    state = 10;
                    continue;
                } else {
                    v___y_1696_ = v___x_1703_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1696_ == 0 {
                    v_ks_1697_ = crate::leanh::lean_ctor_get(v_newNode_1694_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1697_);
                    v_vs_1698_ = crate::leanh::lean_ctor_get(v_newNode_1694_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1698_);
                    crate::leanh::lean_dec_ref(v_newNode_1694_);
                    v___x_1699_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_1701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_x_1638_, v_ks_1697_, v_vs_1698_, v___x_1699_, v___x_1700_);
                    crate::leanh::lean_dec_ref(v_vs_1698_);
                    crate::leanh::lean_dec_ref(v_ks_1697_);
                    return v___x_1701_;
                } else {
                    return v_newNode_1694_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1709_: usize,
    mut v_keys_1710_: *mut crate::leanh::LeanObject,
    mut v_vals_1711_: *mut crate::leanh::LeanObject,
    mut v_i_1712_: *mut crate::leanh::LeanObject,
    mut v_entries_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v_k_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: u64 = 0;
    let mut v_h_1719_: usize = 0;
    let mut v___x_1720_: usize = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: usize = 0;
    let mut v___x_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v_h_1725_: usize = 0;
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1714_ = lean_array_get_size(v_keys_1710_);
                v___x_1715_ = lean_nat_dec_lt(v_i_1712_, v___x_1714_);
                if v___x_1715_ == 0 {
                    crate::leanh::lean_dec(v_i_1712_);
                    return v_entries_1713_;
                } else {
                    v_k_1716_ = lean_array_fget_borrowed(v_keys_1710_, v_i_1712_);
                    v_v_1717_ = lean_array_fget_borrowed(v_vals_1711_, v_i_1712_);
                    v___x_1718_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1716_);
                    v_h_1719_ = lean_uint64_to_usize(v___x_1718_);
                    v___x_1720_ = 5usize;
                    v___x_1721_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1722_ = 1usize;
                    v___x_1723_ = lean_usize_sub(v_depth_1709_, v___x_1722_);
                    v___x_1724_ = lean_usize_mul(v___x_1720_, v___x_1723_);
                    v_h_1725_ = lean_usize_shift_right(v_h_1719_, v___x_1724_);
                    v___x_1726_ = lean_nat_add(v_i_1712_, v___x_1721_);
                    crate::leanh::lean_dec(v_i_1712_);
                    crate::leanh::lean_inc(v_v_1717_);
                    crate::leanh::lean_inc(v_k_1716_);
                    v___x_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_entries_1713_, v_h_1725_, v_depth_1709_, v_k_1716_, v_v_1717_);
                    v_i_1712_ = v___x_1726_;
                    v_entries_1713_ = v___x_1727_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1729_: *mut crate::leanh::LeanObject,
    mut v_keys_1730_: *mut crate::leanh::LeanObject,
    mut v_vals_1731_: *mut crate::leanh::LeanObject,
    mut v_i_1732_: *mut crate::leanh::LeanObject,
    mut v_entries_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1734_: usize = 0;
    let mut v_res_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1734_ = crate::leanh::lean_unbox_usize(v_depth_1729_);
    crate::leanh::lean_dec(v_depth_1729_);
    v_res_1735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1734_, v_keys_1730_, v_vals_1731_, v_i_1732_, v_entries_1733_);
    crate::leanh::lean_dec_ref(v_vals_1731_);
    crate::leanh::lean_dec_ref(v_keys_1730_);
    return v_res_1735_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
    mut v_x_1738_: *mut crate::leanh::LeanObject,
    mut v_x_1739_: *mut crate::leanh::LeanObject,
    mut v_x_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5504__boxed_1741_: usize = 0;
    let mut v_x_5505__boxed_1742_: usize = 0;
    let mut v_res_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5504__boxed_1741_ = crate::leanh::lean_unbox_usize(v_x_1737_);
    crate::leanh::lean_dec(v_x_1737_);
    v_x_5505__boxed_1742_ = crate::leanh::lean_unbox_usize(v_x_1738_);
    crate::leanh::lean_dec(v_x_1738_);
    v_res_1743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_1736_, v_x_5504__boxed_1741_, v_x_5505__boxed_1742_, v_x_1739_, v_x_1740_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(
    mut v_x_1744_: *mut crate::leanh::LeanObject,
    mut v_x_1745_: *mut crate::leanh::LeanObject,
    mut v_x_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: u64 = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1745_);
    v___x_1748_ = lean_uint64_to_usize(v___x_1747_);
    v___x_1749_ = 1usize;
    v___x_1750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_1744_, v___x_1748_, v___x_1749_, v_x_1745_, v_x_1746_);
    return v___x_1750_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0(
    mut v_type_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_s_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMapInv_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_1754_ = crate::leanh::lean_ctor_get(v_s_1753_, 0);
                v_typeIdOf_1755_ = crate::leanh::lean_ctor_get(v_s_1753_, 1);
                v_exprToStructId_1756_ = crate::leanh::lean_ctor_get(v_s_1753_, 2);
                v_termMap_1757_ = crate::leanh::lean_ctor_get(v_s_1753_, 3);
                v_termMapInv_1758_ = crate::leanh::lean_ctor_get(v_s_1753_, 4);
                v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_s_1753_)) as u8;
                if v_isSharedCheck_1766_ == 0 {
                    v___x_1760_ = v_s_1753_;
                    v_isShared_1761_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_termMapInv_1758_);
                    crate::leanh::lean_inc(v_termMap_1757_);
                    crate::leanh::lean_inc(v_exprToStructId_1756_);
                    crate::leanh::lean_inc(v_typeIdOf_1755_);
                    crate::leanh::lean_inc(v_structs_1754_);
                    crate::leanh::lean_dec(v_s_1753_);
                    v___x_1760_ = crate::leanh::lean_box(0);
                    v_isShared_1761_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1762_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_typeIdOf_1755_, v_type_1751_, v_a_1752_);
                if v_isShared_1761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1762_);
                    v___x_1764_ = v___x_1760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_structs_1754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_exprToStructId_1756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_termMap_1757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_termMapInv_1758_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1767_: *mut crate::leanh::LeanObject,
    mut v_vals_1768_: *mut crate::leanh::LeanObject,
    mut v_i_1769_: *mut crate::leanh::LeanObject,
    mut v_k_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1771_ = lean_array_get_size(v_keys_1767_);
                v___x_1772_ = lean_nat_dec_lt(v_i_1769_, v___x_1771_);
                if v___x_1772_ == 0 {
                    crate::leanh::lean_dec(v_i_1769_);
                    v___x_1773_ = crate::leanh::lean_box(0);
                    return v___x_1773_;
                } else {
                    v_k_x27_1774_ = lean_array_fget_borrowed(v_keys_1767_, v_i_1769_);
                    v___x_1775_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1770_,
                            v_k_x27_1774_,
                        );
                    if v___x_1775_ == 0 {
                        v___x_1776_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1777_ = lean_nat_add(v_i_1769_, v___x_1776_);
                        crate::leanh::lean_dec(v_i_1769_);
                        v_i_1769_ = v___x_1777_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1779_ = lean_array_fget_borrowed(v_vals_1768_, v_i_1769_);
                        crate::leanh::lean_dec(v_i_1769_);
                        crate::leanh::lean_inc(v___x_1779_);
                        v___x_1780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1779_);
                        return v___x_1780_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1781_: *mut crate::leanh::LeanObject,
    mut v_vals_1782_: *mut crate::leanh::LeanObject,
    mut v_i_1783_: *mut crate::leanh::LeanObject,
    mut v_k_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1781_, v_vals_1782_, v_i_1783_, v_k_1784_);
    crate::leanh::lean_dec_ref(v_k_1784_);
    crate::leanh::lean_dec_ref(v_vals_1782_);
    crate::leanh::lean_dec_ref(v_keys_1781_);
    return v_res_1785_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(
    mut v_x_1786_: *mut crate::leanh::LeanObject,
    mut v_x_1787_: usize,
    mut v_x_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: usize = 0;
    let mut v___x_1792_: usize = 0;
    let mut v___x_1793_: usize = 0;
    let mut v_j_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: usize = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1786_) == 0 {
                    v_es_1789_ = crate::leanh::lean_ctor_get(v_x_1786_, 0);
                    v___x_1790_ = crate::leanh::lean_box(2);
                    v___x_1791_ = 5usize;
                    v___x_1792_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_1793_ = lean_usize_land(v_x_1787_, v___x_1792_);
                    v_j_1794_ = lean_usize_to_nat(v___x_1793_);
                    v___x_1795_ = lean_array_get_borrowed(v___x_1790_, v_es_1789_, v_j_1794_);
                    crate::leanh::lean_dec(v_j_1794_);
                    match crate::leanh::lean_obj_tag(v___x_1795_) {
                        0 => {
                            v_key_1796_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
                            v_val_1797_ = crate::leanh::lean_ctor_get(v___x_1795_, 1);
                            v___x_1798_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1788_, v_key_1796_);
                            if v___x_1798_ == 0 {
                                v___x_1799_ = crate::leanh::lean_box(0);
                                return v___x_1799_;
                            } else {
                                crate::leanh::lean_inc(v_val_1797_);
                                v___x_1800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1800_, 0, v_val_1797_);
                                return v___x_1800_;
                            }
                        }
                        1 => {
                            v_node_1801_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
                            v___x_1802_ = lean_usize_shift_right(v_x_1787_, v___x_1791_);
                            v_x_1786_ = v_node_1801_;
                            v_x_1787_ = v___x_1802_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1804_ = crate::leanh::lean_box(0);
                            return v___x_1804_;
                        }
                    }
                } else {
                    v_ks_1805_ = crate::leanh::lean_ctor_get(v_x_1786_, 0);
                    v_vs_1806_ = crate::leanh::lean_ctor_get(v_x_1786_, 1);
                    v___x_1807_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1808_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1805_, v_vs_1806_, v___x_1807_, v_x_1788_);
                    return v___x_1808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1809_: *mut crate::leanh::LeanObject,
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5722__boxed_1812_: usize = 0;
    let mut v_res_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5722__boxed_1812_ = crate::leanh::lean_unbox_usize(v_x_1810_);
    crate::leanh::lean_dec(v_x_1810_);
    v_res_1813_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_1809_, v_x_5722__boxed_1812_, v_x_1811_);
    crate::leanh::lean_dec_ref(v_x_1811_);
    crate::leanh::lean_dec_ref(v_x_1809_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(
    mut v_x_1814_: *mut crate::leanh::LeanObject,
    mut v_x_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: u64 = 0;
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1815_);
    v___x_1817_ = lean_uint64_to_usize(v___x_1816_);
    v___x_1818_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_1814_, v___x_1817_, v_x_1815_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg___boxed(
    mut v_x_1819_: *mut crate::leanh::LeanObject,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_1819_, v_x_1820_);
    crate::leanh::lean_dec_ref(v_x_1820_);
    crate::leanh::lean_dec_ref(v_x_1819_);
    return v_res_1821_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId_x3f(
    mut v_type_1822_: *mut crate::leanh::LeanObject,
    mut v_a_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v_order_1839_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v_typeIdOf_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_unused_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1871_: u8 = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_a_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_a_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1834_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1825_);
                if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                    v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1885_ = (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1885_ == 0 {
                        v___x_1837_ = v___x_1834_;
                        v_isShared_1838_ = v_isSharedCheck_1885_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1835_);
                        crate::leanh::lean_dec(v___x_1834_);
                        v___x_1837_ = crate::leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1885_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1822_);
                    v_a_1886_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                    v_isSharedCheck_1893_ = (!crate::leanh::lean_is_exclusive(v___x_1834_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1888_ = v___x_1834_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1886_);
                        crate::leanh::lean_dec(v___x_1834_);
                        v___x_1888_ = crate::leanh::lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_order_1839_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1835_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 27) as u32,
                );
                crate::leanh::lean_dec(v_a_1835_);
                if v_order_1839_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_1822_);
                    v___x_1840_ = crate::leanh::lean_box(0);
                    if v_isShared_1838_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1840_);
                        v___x_1842_ = v___x_1837_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
                        v___x_1842_ = v_reuseFailAlloc_1843_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1837_);
                    v___x_1844_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1823_, v_a_1831_);
                    if crate::leanh::lean_obj_tag(v___x_1844_) == 0 {
                        v_a_1845_ = crate::leanh::lean_ctor_get(v___x_1844_, 0);
                        v_isSharedCheck_1876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1844_)) as u8;
                        if v_isSharedCheck_1876_ == 0 {
                            v___x_1847_ = v___x_1844_;
                            v_isShared_1848_ = v_isSharedCheck_1876_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1845_);
                            crate::leanh::lean_dec(v___x_1844_);
                            v___x_1847_ = crate::leanh::lean_box(0);
                            v_isShared_1848_ = v_isSharedCheck_1876_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1822_);
                        v_a_1877_ = crate::leanh::lean_ctor_get(v___x_1844_, 0);
                        v_isSharedCheck_1884_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1844_)) as u8;
                        if v_isSharedCheck_1884_ == 0 {
                            v___x_1879_ = v___x_1844_;
                            v_isShared_1880_ = v_isSharedCheck_1884_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1877_);
                            crate::leanh::lean_dec(v___x_1844_);
                            v___x_1879_ = crate::leanh::lean_box(0);
                            v_isShared_1880_ = v_isSharedCheck_1884_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1842_;
            }
            3 => {
                v_typeIdOf_1849_ = crate::leanh::lean_ctor_get(v_a_1845_, 1);
                crate::leanh::lean_inc_ref(v_typeIdOf_1849_);
                crate::leanh::lean_dec(v_a_1845_);
                v___x_1850_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_typeIdOf_1849_, v_type_1822_);
                crate::leanh::lean_dec_ref(v_typeIdOf_1849_);
                if crate::leanh::lean_obj_tag(v___x_1850_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_1822_);
                    v_val_1851_ = crate::leanh::lean_ctor_get(v___x_1850_, 0);
                    crate::leanh::lean_inc(v_val_1851_);
                    crate::leanh::lean_dec_ref_known(v___x_1850_, 1);
                    if v_isShared_1848_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1847_, 0, v_val_1851_);
                        v___x_1853_ = v___x_1847_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_val_1851_);
                        v___x_1853_ = v_reuseFailAlloc_1854_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1850_);
                    crate::leanh::lean_del_object(v___x_1847_);
                    crate::leanh::lean_inc_ref(v_type_1822_);
                    v___x_1855_ = l___private_Lean_Meta_Tactic_Grind_Order_StructId_0__Lean_Meta_Grind_Order_getStructId_x3f_go_x3f(v_type_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
                    if crate::leanh::lean_obj_tag(v___x_1855_) == 0 {
                        v_a_1856_ = crate::leanh::lean_ctor_get(v___x_1855_, 0);
                        crate::leanh::lean_inc_n(v_a_1856_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1855_, 1);
                        v___f_1857_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Order_getStructId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1857_, 0, v_type_1822_);
                        crate::leanh::lean_closure_set(v___f_1857_, 1, v_a_1856_);
                        v___x_1858_ = l_Lean_Meta_Grind_Order_orderExt;
                        v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1858_, v___f_1857_, v_a_1823_);
                        if crate::leanh::lean_obj_tag(v___x_1859_) == 0 {
                            v_isSharedCheck_1866_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1859_)) as u8;
                            if v_isSharedCheck_1866_ == 0 {
                                v_unused_1867_ = crate::leanh::lean_ctor_get(v___x_1859_, 0);
                                crate::leanh::lean_dec(v_unused_1867_);
                                v___x_1861_ = v___x_1859_;
                                v_isShared_1862_ = v_isSharedCheck_1866_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1859_);
                                v___x_1861_ = crate::leanh::lean_box(0);
                                v_isShared_1862_ = v_isSharedCheck_1866_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1856_);
                            v_a_1868_ = crate::leanh::lean_ctor_get(v___x_1859_, 0);
                            v_isSharedCheck_1875_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1859_)) as u8;
                            if v_isSharedCheck_1875_ == 0 {
                                v___x_1870_ = v___x_1859_;
                                v_isShared_1871_ = v_isSharedCheck_1875_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1868_);
                                crate::leanh::lean_dec(v___x_1859_);
                                v___x_1870_ = crate::leanh::lean_box(0);
                                v_isShared_1871_ = v_isSharedCheck_1875_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1822_);
                        return v___x_1855_;
                    }
                }
            }
            4 => {
                return v___x_1853_;
            }
            5 => {
                if v_isShared_1862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1861_, 0, v_a_1856_);
                    v___x_1864_ = v___x_1861_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1856_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1864_;
            }
            7 => {
                if v_isShared_1871_ == 0 {
                    v___x_1873_ = v___x_1870_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
                    v___x_1873_ = v_reuseFailAlloc_1874_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1873_;
            }
            9 => {
                if v_isShared_1880_ == 0 {
                    v___x_1882_ = v___x_1879_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
                    v___x_1882_ = v_reuseFailAlloc_1883_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1882_;
            }
            11 => {
                if v_isShared_1889_ == 0 {
                    v___x_1891_ = v___x_1888_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_getStructId_x3f___boxed(
    mut v_type_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lean_Meta_Grind_Order_getStructId_x3f(
        v_type_1894_,
        v_a_1895_,
        v_a_1896_,
        v_a_1897_,
        v_a_1898_,
        v_a_1899_,
        v_a_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
        v_a_1904_,
    );
    crate::leanh::lean_dec(v_a_1904_);
    crate::leanh::lean_dec_ref(v_a_1903_);
    crate::leanh::lean_dec(v_a_1902_);
    crate::leanh::lean_dec_ref(v_a_1901_);
    crate::leanh::lean_dec(v_a_1900_);
    crate::leanh::lean_dec_ref(v_a_1899_);
    crate::leanh::lean_dec(v_a_1898_);
    crate::leanh::lean_dec_ref(v_a_1897_);
    crate::leanh::lean_dec(v_a_1896_);
    crate::leanh::lean_dec(v_a_1895_);
    return v_res_1906_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(
    mut v_00_u03b2_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
    mut v_x_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___redArg(v_x_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0___boxed(
    mut v_00_u03b2_1911_: *mut crate::leanh::LeanObject,
    mut v_x_1912_: *mut crate::leanh::LeanObject,
    mut v_x_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0(
            v_00_u03b2_1911_,
            v_x_1912_,
            v_x_1913_,
        );
    crate::leanh::lean_dec_ref(v_x_1913_);
    crate::leanh::lean_dec_ref(v_x_1912_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1(
    mut v_00_u03b2_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
    mut v_x_1917_: *mut crate::leanh::LeanObject,
    mut v_x_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1___redArg(v_x_1916_, v_x_1917_, v_x_1918_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(
    mut v_00_u03b2_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: usize,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___redArg(v_x_1921_, v_x_1922_, v_x_1923_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1925_: *mut crate::leanh::LeanObject,
    mut v_x_1926_: *mut crate::leanh::LeanObject,
    mut v_x_1927_: *mut crate::leanh::LeanObject,
    mut v_x_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5920__boxed_1929_: usize = 0;
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5920__boxed_1929_ = crate::leanh::lean_unbox_usize(v_x_1927_);
    crate::leanh::lean_dec(v_x_1927_);
    v_res_1930_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0(v_00_u03b2_1925_, v_x_1926_, v_x_5920__boxed_1929_, v_x_1928_);
    crate::leanh::lean_dec_ref(v_x_1928_);
    crate::leanh::lean_dec_ref(v_x_1926_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(
    mut v_00_u03b2_1931_: *mut crate::leanh::LeanObject,
    mut v_x_1932_: *mut crate::leanh::LeanObject,
    mut v_x_1933_: usize,
    mut v_x_1934_: usize,
    mut v_x_1935_: *mut crate::leanh::LeanObject,
    mut v_x_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___redArg(v_x_1932_, v_x_1933_, v_x_1934_, v_x_1935_, v_x_1936_);
    return v___x_1937_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
    mut v_x_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5931__boxed_1944_: usize = 0;
    let mut v_x_5932__boxed_1945_: usize = 0;
    let mut v_res_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5931__boxed_1944_ = crate::leanh::lean_unbox_usize(v_x_1940_);
    crate::leanh::lean_dec(v_x_1940_);
    v_x_5932__boxed_1945_ = crate::leanh::lean_unbox_usize(v_x_1941_);
    crate::leanh::lean_dec(v_x_1941_);
    v_res_1946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2(v_00_u03b2_1938_, v_x_1939_, v_x_5931__boxed_1944_, v_x_5932__boxed_1945_, v_x_1942_, v_x_1943_);
    return v_res_1946_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1947_: *mut crate::leanh::LeanObject,
    mut v_keys_1948_: *mut crate::leanh::LeanObject,
    mut v_vals_1949_: *mut crate::leanh::LeanObject,
    mut v_heq_1950_: *mut crate::leanh::LeanObject,
    mut v_i_1951_: *mut crate::leanh::LeanObject,
    mut v_k_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1948_, v_vals_1949_, v_i_1951_, v_k_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1954_: *mut crate::leanh::LeanObject,
    mut v_keys_1955_: *mut crate::leanh::LeanObject,
    mut v_vals_1956_: *mut crate::leanh::LeanObject,
    mut v_heq_1957_: *mut crate::leanh::LeanObject,
    mut v_i_1958_: *mut crate::leanh::LeanObject,
    mut v_k_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1954_, v_keys_1955_, v_vals_1956_, v_heq_1957_, v_i_1958_, v_k_1959_);
    crate::leanh::lean_dec_ref(v_k_1959_);
    crate::leanh::lean_dec_ref(v_vals_1956_);
    crate::leanh::lean_dec_ref(v_keys_1955_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1961_: *mut crate::leanh::LeanObject,
    mut v_n_1962_: *mut crate::leanh::LeanObject,
    mut v_k_1963_: *mut crate::leanh::LeanObject,
    mut v_v_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4___redArg(v_n_1962_, v_k_1963_, v_v_1964_);
    return v___x_1965_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1966_: *mut crate::leanh::LeanObject,
    mut v_depth_1967_: usize,
    mut v_keys_1968_: *mut crate::leanh::LeanObject,
    mut v_vals_1969_: *mut crate::leanh::LeanObject,
    mut v_heq_1970_: *mut crate::leanh::LeanObject,
    mut v_i_1971_: *mut crate::leanh::LeanObject,
    mut v_entries_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1967_, v_keys_1968_, v_vals_1969_, v_i_1971_, v_entries_1972_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1974_: *mut crate::leanh::LeanObject,
    mut v_depth_1975_: *mut crate::leanh::LeanObject,
    mut v_keys_1976_: *mut crate::leanh::LeanObject,
    mut v_vals_1977_: *mut crate::leanh::LeanObject,
    mut v_heq_1978_: *mut crate::leanh::LeanObject,
    mut v_i_1979_: *mut crate::leanh::LeanObject,
    mut v_entries_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1981_: usize = 0;
    let mut v_res_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1981_ = crate::leanh::lean_unbox_usize(v_depth_1975_);
    crate::leanh::lean_dec(v_depth_1975_);
    v_res_1982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1974_, v_depth_boxed_1981_, v_keys_1976_, v_vals_1977_, v_heq_1978_, v_i_1979_, v_entries_1980_);
    crate::leanh::lean_dec_ref(v_vals_1977_);
    crate::leanh::lean_dec_ref(v_keys_1976_);
    return v_res_1982_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1983_: *mut crate::leanh::LeanObject,
    mut v_x_1984_: *mut crate::leanh::LeanObject,
    mut v_x_1985_: *mut crate::leanh::LeanObject,
    mut v_x_1986_: *mut crate::leanh::LeanObject,
    mut v_x_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Order_getStructId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1984_, v_x_1985_, v_x_1986_, v_x_1987_);
    return v___x_1988_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_StructId(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_StructId(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_StructId(builtin);
}
