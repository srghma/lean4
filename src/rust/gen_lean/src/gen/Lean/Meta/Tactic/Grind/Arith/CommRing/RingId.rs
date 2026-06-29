// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Tactic.Grind.Arith.Insts
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_app___override, l_Lean_mkAppB, l_Lean_mkConst};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_getDecLevel;
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg, l_Lean_Meta_Grind_Arith_CommRing_ringExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Insts::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Insts, l_Lean_Meta_Grind_Arith_getIsCharInst_x3f,
    l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg,
    l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_updateLastTag,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value) as *mut crate::leanh::LeanObject,12221341192526463479 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut crate::leanh::LeanObject,14047490016268445595 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value) as *mut crate::leanh::LeanObject,9499613419783151494 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value) as *mut crate::leanh::LeanObject,8615353994042975301 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [80, 111, 119, 73, 100, 101, 110, 116, 105, 116, 121, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 101, 119, 32, 114, 105, 110, 103, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15814158821706329669 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15814158821706329669 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut crate::leanh::LeanObject,4308150853741380486 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [81, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject,8254287559757149654 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject,12174124158933200568 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [96, 103, 114, 105, 110, 100, 96, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 97, 105, 108, 117, 114, 101, 44, 32, 102, 97, 105, 108, 117, 114, 101, 32, 116, 111, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0);
    v___x_1876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(
    mut v_00_u03b2_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1);
    return v___x_1878_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(
    mut v___x_1882_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1896_: u8 = 0;
    v_options_1895_ = crate::leanh::lean_ctor_get(v___y_1892_, 2);
    v_hasTrace_1896_ = crate::leanh::lean_ctor_get_uint8(
        v_options_1895_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_1896_ == 0 {
        let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1882_);
        v___x_1897_ = crate::leanh::lean_box((v_hasTrace_1896_) as usize);
        v___x_1898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
        return v___x_1898_;
    } else {
        let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: u8 = 0;
        let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1;
        v___x_1900_ = l_Lean_Name_append(v___x_1899_, v___x_1882_);
        v___x_1901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_1883_,
            v_options_1895_,
            v___x_1900_,
        );
        crate::leanh::lean_dec(v___x_1900_);
        v___x_1902_ = crate::leanh::lean_box((v___x_1901_) as usize);
        v___x_1903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
        return v___x_1903_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___boxed(
    mut v___x_1904_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_1904_, v_____do__lift_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
    crate::leanh::lean_dec(v___y_1915_);
    crate::leanh::lean_dec_ref(v___y_1914_);
    crate::leanh::lean_dec(v___y_1913_);
    crate::leanh::lean_dec_ref(v___y_1912_);
    crate::leanh::lean_dec(v___y_1911_);
    crate::leanh::lean_dec_ref(v___y_1910_);
    crate::leanh::lean_dec(v___y_1909_);
    crate::leanh::lean_dec_ref(v___y_1908_);
    crate::leanh::lean_dec(v___y_1907_);
    crate::leanh::lean_dec(v___y_1906_);
    crate::leanh::lean_dec_ref(v_____do__lift_1905_);
    return v_res_1917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1(
    mut v___x_1918_: *mut crate::leanh::LeanObject,
    mut v_s_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_1933_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_1920_ = crate::leanh::lean_ctor_get(v_s_1919_, 0);
                v_typeIdOf_1921_ = crate::leanh::lean_ctor_get(v_s_1919_, 1);
                v_exprToRingId_1922_ = crate::leanh::lean_ctor_get(v_s_1919_, 2);
                v_semirings_1923_ = crate::leanh::lean_ctor_get(v_s_1919_, 3);
                v_stypeIdOf_1924_ = crate::leanh::lean_ctor_get(v_s_1919_, 4);
                v_exprToSemiringId_1925_ = crate::leanh::lean_ctor_get(v_s_1919_, 5);
                v_ncRings_1926_ = crate::leanh::lean_ctor_get(v_s_1919_, 6);
                v_exprToNCRingId_1927_ = crate::leanh::lean_ctor_get(v_s_1919_, 7);
                v_nctypeIdOf_1928_ = crate::leanh::lean_ctor_get(v_s_1919_, 8);
                v_ncSemirings_1929_ = crate::leanh::lean_ctor_get(v_s_1919_, 9);
                v_exprToNCSemiringId_1930_ = crate::leanh::lean_ctor_get(v_s_1919_, 10);
                v_ncstypeIdOf_1931_ = crate::leanh::lean_ctor_get(v_s_1919_, 11);
                v_steps_1932_ = crate::leanh::lean_ctor_get(v_s_1919_, 12);
                v_reportedMaxDegreeIssue_1933_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_1941_ = (!crate::leanh::lean_is_exclusive(v_s_1919_)) as u8;
                if v_isSharedCheck_1941_ == 0 {
                    v___x_1935_ = v_s_1919_;
                    v_isShared_1936_ = v_isSharedCheck_1941_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_1932_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_1931_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_1930_);
                    crate::leanh::lean_inc(v_ncSemirings_1929_);
                    crate::leanh::lean_inc(v_nctypeIdOf_1928_);
                    crate::leanh::lean_inc(v_exprToNCRingId_1927_);
                    crate::leanh::lean_inc(v_ncRings_1926_);
                    crate::leanh::lean_inc(v_exprToSemiringId_1925_);
                    crate::leanh::lean_inc(v_stypeIdOf_1924_);
                    crate::leanh::lean_inc(v_semirings_1923_);
                    crate::leanh::lean_inc(v_exprToRingId_1922_);
                    crate::leanh::lean_inc(v_typeIdOf_1921_);
                    crate::leanh::lean_inc(v_rings_1920_);
                    crate::leanh::lean_dec(v_s_1919_);
                    v___x_1935_ = crate::leanh::lean_box(0);
                    v_isShared_1936_ = v_isSharedCheck_1941_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1937_ = lean_array_push(v_rings_1920_, v___x_1918_);
                if v_isShared_1936_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1935_, 0, v___x_1937_);
                    v___x_1939_ = v___x_1935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_typeIdOf_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_exprToRingId_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_semirings_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_stypeIdOf_1924_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1940_,
                        5,
                        v_exprToSemiringId_1925_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_ncRings_1926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_exprToNCRingId_1927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_nctypeIdOf_1928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 9, v_ncSemirings_1929_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1940_,
                        10,
                        v_exprToNCSemiringId_1930_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 11, v_ncstypeIdOf_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 12, v_steps_1932_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1940_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_1933_,
                    );
                    v___x_1939_ = v_reuseFailAlloc_1940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(
    mut v_msgData_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_st_ref_get(v___y_1946_);
    v_env_1949_ = crate::leanh::lean_ctor_get(v___x_1948_, 0);
    crate::leanh::lean_inc_ref(v_env_1949_);
    crate::leanh::lean_dec(v___x_1948_);
    v___x_1950_ = lean_st_ref_get(v___y_1944_);
    v_mctx_1951_ = crate::leanh::lean_ctor_get(v___x_1950_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1951_);
    crate::leanh::lean_dec(v___x_1950_);
    v_lctx_1952_ = crate::leanh::lean_ctor_get(v___y_1943_, 2);
    v_options_1953_ = crate::leanh::lean_ctor_get(v___y_1945_, 2);
    crate::leanh::lean_inc_ref(v_options_1953_);
    crate::leanh::lean_inc_ref(v_lctx_1952_);
    v___x_1954_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1954_, 0, v_env_1949_);
    crate::leanh::lean_ctor_set(v___x_1954_, 1, v_mctx_1951_);
    crate::leanh::lean_ctor_set(v___x_1954_, 2, v_lctx_1952_);
    crate::leanh::lean_ctor_set(v___x_1954_, 3, v_options_1953_);
    v___x_1955_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
    crate::leanh::lean_ctor_set(v___x_1955_, 1, v_msgData_1942_);
    v___x_1956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(
    mut v_msgData_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msgData_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
    crate::leanh::lean_dec(v___y_1961_);
    crate::leanh::lean_dec_ref(v___y_1960_);
    crate::leanh::lean_dec(v___y_1959_);
    crate::leanh::lean_dec_ref(v___y_1958_);
    return v_res_1963_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: f64 = 0.0;
    v___x_1964_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1965_ = lean_float_of_nat(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(
    mut v_cls_1969_: *mut crate::leanh::LeanObject,
    mut v_msg_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v_tid_1995_: u64 = 0;
    let mut v_traces_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: f64 = 0.0;
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1976_ = crate::leanh::lean_ctor_get(v___y_1973_, 5);
                v___x_1977_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
                v_a_1978_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
                v_isSharedCheck_2022_ = (!crate::leanh::lean_is_exclusive(v___x_1977_)) as u8;
                if v_isSharedCheck_2022_ == 0 {
                    v___x_1980_ = v___x_1977_;
                    v_isShared_1981_ = v_isSharedCheck_2022_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1978_);
                    crate::leanh::lean_dec(v___x_1977_);
                    v___x_1980_ = crate::leanh::lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_2022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = lean_st_ref_take(v___y_1974_);
                v_traceState_1983_ = crate::leanh::lean_ctor_get(v___x_1982_, 4);
                v_env_1984_ = crate::leanh::lean_ctor_get(v___x_1982_, 0);
                v_nextMacroScope_1985_ = crate::leanh::lean_ctor_get(v___x_1982_, 1);
                v_ngen_1986_ = crate::leanh::lean_ctor_get(v___x_1982_, 2);
                v_auxDeclNGen_1987_ = crate::leanh::lean_ctor_get(v___x_1982_, 3);
                v_cache_1988_ = crate::leanh::lean_ctor_get(v___x_1982_, 5);
                v_messages_1989_ = crate::leanh::lean_ctor_get(v___x_1982_, 6);
                v_infoState_1990_ = crate::leanh::lean_ctor_get(v___x_1982_, 7);
                v_snapshotTasks_1991_ = crate::leanh::lean_ctor_get(v___x_1982_, 8);
                v_isSharedCheck_2021_ = (!crate::leanh::lean_is_exclusive(v___x_1982_)) as u8;
                if v_isSharedCheck_2021_ == 0 {
                    v___x_1993_ = v___x_1982_;
                    v_isShared_1994_ = v_isSharedCheck_2021_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1991_);
                    crate::leanh::lean_inc(v_infoState_1990_);
                    crate::leanh::lean_inc(v_messages_1989_);
                    crate::leanh::lean_inc(v_cache_1988_);
                    crate::leanh::lean_inc(v_traceState_1983_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1987_);
                    crate::leanh::lean_inc(v_ngen_1986_);
                    crate::leanh::lean_inc(v_nextMacroScope_1985_);
                    crate::leanh::lean_inc(v_env_1984_);
                    crate::leanh::lean_dec(v___x_1982_);
                    v___x_1993_ = crate::leanh::lean_box(0);
                    v_isShared_1994_ = v_isSharedCheck_2021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1995_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1983_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1996_ = crate::leanh::lean_ctor_get(v_traceState_1983_, 0);
                v_isSharedCheck_2020_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1983_)) as u8;
                if v_isSharedCheck_2020_ == 0 {
                    v___x_1998_ = v_traceState_1983_;
                    v_isShared_1999_ = v_isSharedCheck_2020_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1996_);
                    crate::leanh::lean_dec(v_traceState_1983_);
                    v___x_1998_ = crate::leanh::lean_box(0);
                    v_isShared_1999_ = v_isSharedCheck_2020_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2000_ = crate::leanh::lean_box(0);
                v___x_2001_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0);
                v___x_2002_ = 0;
                v___x_2003_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1;
                v___x_2004_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2004_, 0, v_cls_1969_);
                crate::leanh::lean_ctor_set(v___x_2004_, 1, v___x_2000_);
                crate::leanh::lean_ctor_set(v___x_2004_, 2, v___x_2003_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2001_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2001_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2002_,
                );
                v___x_2005_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2;
                v___x_2006_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2006_, 0, v___x_2004_);
                crate::leanh::lean_ctor_set(v___x_2006_, 1, v_a_1978_);
                crate::leanh::lean_ctor_set(v___x_2006_, 2, v___x_2005_);
                crate::leanh::lean_inc(v_ref_1976_);
                v___x_2007_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2007_, 0, v_ref_1976_);
                crate::leanh::lean_ctor_set(v___x_2007_, 1, v___x_2006_);
                v___x_2008_ = l_Lean_PersistentArray_push___redArg(v_traces_1996_, v___x_2007_);
                if v_isShared_1999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1998_, 0, v___x_2008_);
                    v___x_2010_ = v___x_1998_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2008_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2019_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1995_,
                    );
                    v___x_2010_ = v_reuseFailAlloc_2019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 4, v___x_2010_);
                    v___x_2012_ = v___x_1993_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_env_1984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_nextMacroScope_1985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_ngen_1986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_auxDeclNGen_1987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 4, v___x_2010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_cache_1988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_messages_1989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_infoState_1990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_snapshotTasks_1991_);
                    v___x_2012_ = v_reuseFailAlloc_2018_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2013_ = lean_st_ref_set(v___y_1974_, v___x_2012_);
                v___x_2014_ = crate::leanh::lean_box(0);
                if v_isShared_1981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_2014_);
                    v___x_2016_ = v___x_1980_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
                    v___x_2016_ = v_reuseFailAlloc_2017_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___boxed(
    mut v_cls_2023_: *mut crate::leanh::LeanObject,
    mut v_msg_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_2023_, v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
    crate::leanh::lean_dec(v___y_2028_);
    crate::leanh::lean_dec_ref(v___y_2027_);
    crate::leanh::lean_dec(v___y_2026_);
    crate::leanh::lean_dec_ref(v___y_2025_);
    return v_res_2030_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2063_ = lean_mk_empty_array_with_capacity(v___x_2062_);
    v___x_2064_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    return v___x_2064_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: usize = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = 5usize;
    v___x_2066_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2067_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2068_ = lean_mk_empty_array_with_capacity(v___x_2067_);
    v___x_2069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
    v___x_2070_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2070_, 0, v___x_2069_);
    crate::leanh::lean_ctor_set(v___x_2070_, 1, v___x_2068_);
    crate::leanh::lean_ctor_set(v___x_2070_, 2, v___x_2066_);
    crate::leanh::lean_ctor_set(v___x_2070_, 3, v___x_2066_);
    crate::leanh::lean_ctor_set_usize(v___x_2070_, 4, v___x_2065_);
    return v___x_2070_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
    v___x_2073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2073_, 0, v___x_2072_);
    return v___x_2073_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(crate::leanh::lean_box(0));
    return v___x_2074_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6;
    v___x_2081_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1;
    v___x_2082_ = l_Lean_Name_append(v___x_2081_, v___x_2080_);
    return v___x_2082_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22;
    v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
    return v___x_2085_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26;
    v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28;
    v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
    return v___x_2093_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(
    mut v_type_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
    mut v_a_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v_val_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v_inheritedTraceOptions_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_unused_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v___y_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2239_: u8 = 0;
    let mut v_a_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_a_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2260_: u8 = 0;
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_a_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut v___y_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v___y_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_a_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut v_isSharedCheck_2369_: u8 = 0;
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_a_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2094_);
                v___x_2106_ = l_Lean_Meta_getDecLevel(
                    v_type_2094_,
                    v_a_2101_,
                    v_a_2102_,
                    v_a_2103_,
                    v_a_2104_,
                );
                if crate::leanh::lean_obj_tag(v___x_2106_) == 0 {
                    v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                    crate::leanh::lean_inc_n(v_a_2107_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2106_, 1);
                    v___x_2108_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3;
                    v___x_2109_ = crate::leanh::lean_box(0);
                    v___x_2110_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2110_, 0, v_a_2107_);
                    crate::leanh::lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                    crate::leanh::lean_inc_ref(v___x_2110_);
                    v___x_2111_ = l_Lean_mkConst(v___x_2108_, v___x_2110_);
                    crate::leanh::lean_inc_ref(v_type_2094_);
                    v___x_2112_ = l_Lean_Expr_app___override(v___x_2111_, v_type_2094_);
                    v___x_2113_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2112_,
                        v_a_2101_,
                        v_a_2102_,
                        v_a_2103_,
                        v_a_2104_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        v_isSharedCheck_2375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2375_ == 0 {
                            v___x_2116_ = v___x_2113_;
                            v_isShared_2117_ = v_isSharedCheck_2375_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2114_);
                            crate::leanh::lean_dec(v___x_2113_);
                            v___x_2116_ = crate::leanh::lean_box(0);
                            v_isShared_2117_ = v_isSharedCheck_2375_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                        crate::leanh::lean_dec(v_a_2107_);
                        crate::leanh::lean_dec_ref(v_type_2094_);
                        v_a_2376_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        v_isSharedCheck_2383_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2383_ == 0 {
                            v___x_2378_ = v___x_2113_;
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2376_);
                            crate::leanh::lean_dec(v___x_2113_);
                            v___x_2378_ = crate::leanh::lean_box(0);
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2384_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                    v_isSharedCheck_2391_ = (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                    if v_isSharedCheck_2391_ == 0 {
                        v___x_2386_ = v___x_2106_;
                        v_isShared_2387_ = v_isSharedCheck_2391_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2384_);
                        crate::leanh::lean_dec(v___x_2106_);
                        v___x_2386_ = crate::leanh::lean_box(0);
                        v_isShared_2387_ = v_isSharedCheck_2391_;
                        state = 40;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2114_) == 1 {
                    crate::leanh::lean_del_object(v___x_2116_);
                    v_val_2118_ = crate::leanh::lean_ctor_get(v_a_2114_, 0);
                    v_isSharedCheck_2370_ = (!crate::leanh::lean_is_exclusive(v_a_2114_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2120_ = v_a_2114_;
                        v_isShared_2121_ = v_isSharedCheck_2370_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2118_);
                        crate::leanh::lean_dec(v_a_2114_);
                        v___x_2120_ = crate::leanh::lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2370_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2114_);
                    crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v___x_2371_ = crate::leanh::lean_box(0);
                    if v_isShared_2117_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2116_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2116_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 37;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2122_ = crate::leanh::lean_ctor_get(v_a_2103_, 13);
                v___x_2123_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6;
                v___x_2124_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_2123_, v_inheritedTraceOptions_2122_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
                v_a_2125_ = crate::leanh::lean_ctor_get(v___x_2124_, 0);
                v_isSharedCheck_2369_ = (!crate::leanh::lean_is_exclusive(v___x_2124_)) as u8;
                if v_isSharedCheck_2369_ == 0 {
                    v___x_2127_ = v___x_2124_;
                    v_isShared_2128_ = v_isSharedCheck_2369_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2125_);
                    crate::leanh::lean_dec(v___x_2124_);
                    v___x_2127_ = crate::leanh::lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2369_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2129_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8;
                crate::leanh::lean_inc_ref_n(v___x_2110_, 3);
                v___x_2130_ = l_Lean_mkConst(v___x_2129_, v___x_2110_);
                crate::leanh::lean_inc(v_val_2118_);
                crate::leanh::lean_inc_ref_n(v_type_2094_, 3);
                v___x_2131_ = l_Lean_mkAppB(v___x_2130_, v_type_2094_, v_val_2118_);
                v___x_2132_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11;
                v___x_2133_ = l_Lean_mkConst(v___x_2132_, v___x_2110_);
                crate::leanh::lean_inc_ref(v___x_2131_);
                v___x_2134_ = l_Lean_mkAppB(v___x_2133_, v_type_2094_, v___x_2131_);
                v___x_2135_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13;
                v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2110_);
                crate::leanh::lean_inc_ref(v___x_2134_);
                v___x_2137_ = l_Lean_mkAppB(v___x_2136_, v_type_2094_, v___x_2134_);
                v___x_2347_ = (crate::leanh::lean_unbox(v_a_2125_) as u8);
                crate::leanh::lean_dec(v_a_2125_);
                if v___x_2347_ == 0 {
                    v___y_2301_ = v_a_2095_;
                    v___y_2302_ = v_a_2096_;
                    v___y_2303_ = v_a_2097_;
                    v___y_2304_ = v_a_2098_;
                    v___y_2305_ = v_a_2099_;
                    v___y_2306_ = v_a_2100_;
                    v___y_2307_ = v_a_2101_;
                    v___y_2308_ = v_a_2102_;
                    v___y_2309_ = v_a_2103_;
                    v___y_2310_ = v_a_2104_;
                    state = 26;
                    continue;
                } else {
                    v___x_2348_ = l_Lean_Meta_Grind_updateLastTag(
                        v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_,
                        v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2348_, 1);
                        v___x_2349_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
                        crate::leanh::lean_inc_ref(v_type_2094_);
                        v___x_2350_ = l_Lean_MessageData_ofExpr(v_type_2094_);
                        v___x_2351_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2349_);
                        crate::leanh::lean_ctor_set(v___x_2351_, 1, v___x_2350_);
                        v___x_2352_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2351_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
                        if crate::leanh::lean_obj_tag(v___x_2352_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2352_, 1);
                            v___y_2301_ = v_a_2095_;
                            v___y_2302_ = v_a_2096_;
                            v___y_2303_ = v_a_2097_;
                            v___y_2304_ = v_a_2098_;
                            v___y_2305_ = v_a_2099_;
                            v___y_2306_ = v_a_2100_;
                            v___y_2307_ = v_a_2101_;
                            v___y_2308_ = v_a_2102_;
                            v___y_2309_ = v_a_2103_;
                            v___y_2310_ = v_a_2104_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2137_);
                            crate::leanh::lean_dec_ref(v___x_2134_);
                            crate::leanh::lean_dec_ref(v___x_2131_);
                            crate::leanh::lean_del_object(v___x_2127_);
                            crate::leanh::lean_del_object(v___x_2120_);
                            crate::leanh::lean_dec(v_val_2118_);
                            crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                            crate::leanh::lean_dec(v_a_2107_);
                            crate::leanh::lean_dec_ref(v_type_2094_);
                            v_a_2353_ = crate::leanh::lean_ctor_get(v___x_2352_, 0);
                            v_isSharedCheck_2360_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2352_)) as u8;
                            if v_isSharedCheck_2360_ == 0 {
                                v___x_2355_ = v___x_2352_;
                                v_isShared_2356_ = v_isSharedCheck_2360_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2353_);
                                crate::leanh::lean_dec(v___x_2352_);
                                v___x_2355_ = crate::leanh::lean_box(0);
                                v_isShared_2356_ = v_isSharedCheck_2360_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2137_);
                        crate::leanh::lean_dec_ref(v___x_2134_);
                        crate::leanh::lean_dec_ref(v___x_2131_);
                        crate::leanh::lean_del_object(v___x_2127_);
                        crate::leanh::lean_del_object(v___x_2120_);
                        crate::leanh::lean_dec(v_val_2118_);
                        crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                        crate::leanh::lean_dec(v_a_2107_);
                        crate::leanh::lean_dec_ref(v_type_2094_);
                        v_a_2361_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2368_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2368_ == 0 {
                            v___x_2363_ = v___x_2348_;
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2361_);
                            crate::leanh::lean_dec(v___x_2348_);
                            v___x_2363_ = crate::leanh::lean_box(0);
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 35;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_2145_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_2143_, v___y_2144_);
                if crate::leanh::lean_obj_tag(v___x_2145_) == 0 {
                    v_a_2146_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
                    crate::leanh::lean_inc(v_a_2146_);
                    crate::leanh::lean_dec_ref_known(v___x_2145_, 1);
                    v_rings_2147_ = crate::leanh::lean_ctor_get(v_a_2146_, 0);
                    crate::leanh::lean_inc_ref(v_rings_2147_);
                    crate::leanh::lean_dec(v_a_2146_);
                    v___x_2148_ = crate::leanh::lean_box(0);
                    v___x_2149_ = lean_array_get_size(v_rings_2147_);
                    crate::leanh::lean_dec_ref(v_rings_2147_);
                    v___x_2150_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_2152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
                    v___x_2153_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2149_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 1, v_type_2094_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 2, v_a_2107_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 3, v___x_2131_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 4, v___x_2134_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 5, v___y_2142_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 6, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 7, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 8, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 9, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 10, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 11, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 12, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 13, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 14, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 15, v___x_2152_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 16, v___x_2152_);
                    v___x_2154_ = crate::leanh::lean_box(1);
                    v___x_2155_ = 0;
                    v___x_2156_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18);
                    v___x_2157_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 1, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 2, v___x_2148_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 3, v___x_2137_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 4, v_val_2118_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 5, v___y_2139_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 6, v___y_2141_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 7, v___y_2140_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 8, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 9, v___x_2150_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 10, v___x_2150_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 11, v___x_2154_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 12, v___x_2109_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 13, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 14, v___x_2156_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 15, v___x_2150_);
                    crate::leanh::lean_ctor_set(v___x_2157_, 16, v___x_2148_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v___x_2155_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v___x_2155_,
                    );
                    v___f_2158_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2158_, 0, v___x_2157_);
                    v___x_2159_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_2160_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2159_, v___f_2158_, v___y_2143_);
                    if crate::leanh::lean_obj_tag(v___x_2160_) == 0 {
                        v_isSharedCheck_2170_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2160_)) as u8;
                        if v_isSharedCheck_2170_ == 0 {
                            v_unused_2171_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                            crate::leanh::lean_dec(v_unused_2171_);
                            v___x_2162_ = v___x_2160_;
                            v_isShared_2163_ = v_isSharedCheck_2170_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2160_);
                            v___x_2162_ = crate::leanh::lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2170_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2120_);
                        v_a_2172_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                        v_isSharedCheck_2179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2160_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v___x_2174_ = v___x_2160_;
                            v_isShared_2175_ = v_isSharedCheck_2179_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2172_);
                            crate::leanh::lean_dec(v___x_2160_);
                            v___x_2174_ = crate::leanh::lean_box(0);
                            v_isShared_2175_ = v_isSharedCheck_2179_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2142_);
                    crate::leanh::lean_dec(v___y_2141_);
                    crate::leanh::lean_dec(v___y_2140_);
                    crate::leanh::lean_dec(v___y_2139_);
                    crate::leanh::lean_dec_ref(v___x_2137_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    crate::leanh::lean_dec_ref(v___x_2131_);
                    crate::leanh::lean_del_object(v___x_2120_);
                    crate::leanh::lean_dec(v_val_2118_);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2180_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
                    v_isSharedCheck_2187_ = (!crate::leanh::lean_is_exclusive(v___x_2145_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2182_ = v___x_2145_;
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2180_);
                        crate::leanh::lean_dec(v___x_2145_);
                        v___x_2182_ = crate::leanh::lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2149_);
                    v___x_2165_ = v___x_2120_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2149_);
                    v___x_2165_ = v_reuseFailAlloc_2169_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2165_);
                    v___x_2167_ = v___x_2162_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2167_;
            }
            8 => {
                if v_isShared_2175_ == 0 {
                    v___x_2177_ = v___x_2174_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
                    v___x_2177_ = v_reuseFailAlloc_2178_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2177_;
            }
            10 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2185_;
            }
            12 => {
                crate::leanh::lean_inc_ref(v___y_2204_);
                if v_isShared_2128_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2127_, 3);
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___y_2204_);
                    v___x_2206_ = v___x_2127_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___y_2204_);
                    v___x_2206_ = v_reuseFailAlloc_2218_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2207_ = l_Lean_MessageData_ofFormat(v___x_2206_);
                crate::leanh::lean_inc_ref(v___y_2202_);
                v___x_2208_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2208_, 0, v___y_2202_);
                crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
                v___x_2209_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2208_, v___y_2191_, v___y_2194_, v___y_2203_, v___y_2192_);
                if crate::leanh::lean_obj_tag(v___x_2209_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2209_, 1);
                    v___y_2139_ = v___y_2193_;
                    v___y_2140_ = v___y_2200_;
                    v___y_2141_ = v___y_2196_;
                    v___y_2142_ = v___y_2197_;
                    v___y_2143_ = v___y_2198_;
                    v___y_2144_ = v___y_2203_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2200_);
                    crate::leanh::lean_dec(v___y_2197_);
                    crate::leanh::lean_dec(v___y_2196_);
                    crate::leanh::lean_dec(v___y_2193_);
                    crate::leanh::lean_dec_ref(v___x_2137_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    crate::leanh::lean_dec_ref(v___x_2131_);
                    crate::leanh::lean_del_object(v___x_2120_);
                    crate::leanh::lean_dec(v_val_2118_);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2210_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                    v_isSharedCheck_2217_ = (!crate::leanh::lean_is_exclusive(v___x_2209_)) as u8;
                    if v_isSharedCheck_2217_ == 0 {
                        v___x_2212_ = v___x_2209_;
                        v_isShared_2213_ = v_isSharedCheck_2217_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2210_);
                        crate::leanh::lean_dec(v___x_2209_);
                        v___x_2212_ = crate::leanh::lean_box(0);
                        v_isShared_2213_ = v_isSharedCheck_2217_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2213_ == 0 {
                    v___x_2215_ = v___x_2212_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2215_;
            }
            16 => {
                v___x_2232_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20;
                v___x_2233_ = l_Lean_mkConst(v___x_2232_, v___x_2110_);
                crate::leanh::lean_inc_ref(v_type_2094_);
                v___x_2234_ = l_Lean_Expr_app___override(v___x_2233_, v_type_2094_);
                v___x_2235_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_2234_,
                    v___y_2228_,
                    v___y_2229_,
                    v___y_2230_,
                    v___y_2231_,
                );
                if crate::leanh::lean_obj_tag(v___x_2235_) == 0 {
                    v_a_2236_ = crate::leanh::lean_ctor_get(v___x_2235_, 0);
                    crate::leanh::lean_inc(v_a_2236_);
                    crate::leanh::lean_dec_ref_known(v___x_2235_, 1);
                    crate::leanh::lean_inc_ref(v_type_2094_);
                    crate::leanh::lean_inc(v_a_2107_);
                    v___x_2237_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(
                        v_a_2107_,
                        v_type_2094_,
                        v___y_2222_,
                        v___y_2223_,
                        v___y_2224_,
                        v___y_2225_,
                        v___y_2226_,
                        v___y_2227_,
                        v___y_2228_,
                        v___y_2229_,
                        v___y_2230_,
                        v___y_2231_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2237_) == 0 {
                        v_options_2238_ = crate::leanh::lean_ctor_get(v___y_2230_, 2);
                        v_hasTrace_2239_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_2238_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2239_ == 0 {
                            crate::leanh::lean_del_object(v___x_2127_);
                            v_a_2240_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
                            crate::leanh::lean_inc(v_a_2240_);
                            crate::leanh::lean_dec_ref_known(v___x_2237_, 1);
                            v___y_2139_ = v___y_2220_;
                            v___y_2140_ = v_a_2240_;
                            v___y_2141_ = v_a_2236_;
                            v___y_2142_ = v___y_2221_;
                            v___y_2143_ = v___y_2222_;
                            v___y_2144_ = v___y_2230_;
                            state = 4;
                            continue;
                        } else {
                            v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
                            crate::leanh::lean_inc(v_a_2241_);
                            crate::leanh::lean_dec_ref_known(v___x_2237_, 1);
                            v_inheritedTraceOptions_2242_ =
                                crate::leanh::lean_ctor_get(v___y_2230_, 13);
                            v___x_2243_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
                            v___x_2244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2242_,
                                v_options_2238_,
                                v___x_2243_,
                            );
                            if v___x_2244_ == 0 {
                                crate::leanh::lean_del_object(v___x_2127_);
                                v___y_2139_ = v___y_2220_;
                                v___y_2140_ = v_a_2241_;
                                v___y_2141_ = v_a_2236_;
                                v___y_2142_ = v___y_2221_;
                                v___y_2143_ = v___y_2222_;
                                v___y_2144_ = v___y_2230_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2245_ = l_Lean_Meta_Grind_updateLastTag(
                                    v___y_2222_,
                                    v___y_2223_,
                                    v___y_2224_,
                                    v___y_2225_,
                                    v___y_2226_,
                                    v___y_2227_,
                                    v___y_2228_,
                                    v___y_2229_,
                                    v___y_2230_,
                                    v___y_2231_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2245_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2245_, 1);
                                    v___x_2246_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
                                    if crate::leanh::lean_obj_tag(v_a_2241_) == 0 {
                                        v___x_2247_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24;
                                        v___y_2189_ = v___y_2226_;
                                        v___y_2190_ = v___y_2225_;
                                        v___y_2191_ = v___y_2228_;
                                        v___y_2192_ = v___y_2231_;
                                        v___y_2193_ = v___y_2220_;
                                        v___y_2194_ = v___y_2229_;
                                        v___y_2195_ = v___y_2223_;
                                        v___y_2196_ = v_a_2236_;
                                        v___y_2197_ = v___y_2221_;
                                        v___y_2198_ = v___y_2222_;
                                        v___y_2199_ = v___y_2227_;
                                        v___y_2200_ = v_a_2241_;
                                        v___y_2201_ = v___y_2224_;
                                        v___y_2202_ = v___x_2246_;
                                        v___y_2203_ = v___y_2230_;
                                        v___y_2204_ = v___x_2247_;
                                        state = 12;
                                        continue;
                                    } else {
                                        v___x_2248_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25;
                                        v___y_2189_ = v___y_2226_;
                                        v___y_2190_ = v___y_2225_;
                                        v___y_2191_ = v___y_2228_;
                                        v___y_2192_ = v___y_2231_;
                                        v___y_2193_ = v___y_2220_;
                                        v___y_2194_ = v___y_2229_;
                                        v___y_2195_ = v___y_2223_;
                                        v___y_2196_ = v_a_2236_;
                                        v___y_2197_ = v___y_2221_;
                                        v___y_2198_ = v___y_2222_;
                                        v___y_2199_ = v___y_2227_;
                                        v___y_2200_ = v_a_2241_;
                                        v___y_2201_ = v___y_2224_;
                                        v___y_2202_ = v___x_2246_;
                                        v___y_2203_ = v___y_2230_;
                                        v___y_2204_ = v___x_2248_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2241_);
                                    crate::leanh::lean_dec(v_a_2236_);
                                    crate::leanh::lean_dec(v___y_2221_);
                                    crate::leanh::lean_dec(v___y_2220_);
                                    crate::leanh::lean_dec_ref(v___x_2137_);
                                    crate::leanh::lean_dec_ref(v___x_2134_);
                                    crate::leanh::lean_dec_ref(v___x_2131_);
                                    crate::leanh::lean_del_object(v___x_2127_);
                                    crate::leanh::lean_del_object(v___x_2120_);
                                    crate::leanh::lean_dec(v_val_2118_);
                                    crate::leanh::lean_dec(v_a_2107_);
                                    crate::leanh::lean_dec_ref(v_type_2094_);
                                    v_a_2249_ = crate::leanh::lean_ctor_get(v___x_2245_, 0);
                                    v_isSharedCheck_2256_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2245_)) as u8;
                                    if v_isSharedCheck_2256_ == 0 {
                                        v___x_2251_ = v___x_2245_;
                                        v_isShared_2252_ = v_isSharedCheck_2256_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2249_);
                                        crate::leanh::lean_dec(v___x_2245_);
                                        v___x_2251_ = crate::leanh::lean_box(0);
                                        v_isShared_2252_ = v_isSharedCheck_2256_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2236_);
                        crate::leanh::lean_dec(v___y_2221_);
                        crate::leanh::lean_dec(v___y_2220_);
                        crate::leanh::lean_dec_ref(v___x_2137_);
                        crate::leanh::lean_dec_ref(v___x_2134_);
                        crate::leanh::lean_dec_ref(v___x_2131_);
                        crate::leanh::lean_del_object(v___x_2127_);
                        crate::leanh::lean_del_object(v___x_2120_);
                        crate::leanh::lean_dec(v_val_2118_);
                        crate::leanh::lean_dec(v_a_2107_);
                        crate::leanh::lean_dec_ref(v_type_2094_);
                        v_a_2257_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
                        v_isSharedCheck_2264_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2237_)) as u8;
                        if v_isSharedCheck_2264_ == 0 {
                            v___x_2259_ = v___x_2237_;
                            v_isShared_2260_ = v_isSharedCheck_2264_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2257_);
                            crate::leanh::lean_dec(v___x_2237_);
                            v___x_2259_ = crate::leanh::lean_box(0);
                            v_isShared_2260_ = v_isSharedCheck_2264_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2221_);
                    crate::leanh::lean_dec(v___y_2220_);
                    crate::leanh::lean_dec_ref(v___x_2137_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    crate::leanh::lean_dec_ref(v___x_2131_);
                    crate::leanh::lean_del_object(v___x_2127_);
                    crate::leanh::lean_del_object(v___x_2120_);
                    crate::leanh::lean_dec(v_val_2118_);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2265_ = crate::leanh::lean_ctor_get(v___x_2235_, 0);
                    v_isSharedCheck_2272_ = (!crate::leanh::lean_is_exclusive(v___x_2235_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2235_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2265_);
                        crate::leanh::lean_dec(v___x_2235_);
                        v___x_2267_ = crate::leanh::lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 21;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_2252_ == 0 {
                    v___x_2254_ = v___x_2251_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
                    v___x_2254_ = v_reuseFailAlloc_2255_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2254_;
            }
            19 => {
                if v_isShared_2260_ == 0 {
                    v___x_2262_ = v___x_2259_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
                    v___x_2262_ = v_reuseFailAlloc_2263_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2262_;
            }
            21 => {
                if v_isShared_2268_ == 0 {
                    v___x_2270_ = v___x_2267_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2270_;
            }
            23 => {
                crate::leanh::lean_inc_ref(v___y_2287_);
                v___x_2288_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2288_, 0, v___y_2287_);
                v___x_2289_ = l_Lean_MessageData_ofFormat(v___x_2288_);
                crate::leanh::lean_inc_ref(v___y_2274_);
                v___x_2290_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2290_, 0, v___y_2274_);
                crate::leanh::lean_ctor_set(v___x_2290_, 1, v___x_2289_);
                v___x_2291_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2290_, v___y_2285_, v___y_2282_, v___y_2275_, v___y_2277_);
                if crate::leanh::lean_obj_tag(v___x_2291_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2291_, 1);
                    v___y_2220_ = v___y_2276_;
                    v___y_2221_ = v___y_2281_;
                    v___y_2222_ = v___y_2278_;
                    v___y_2223_ = v___y_2283_;
                    v___y_2224_ = v___y_2280_;
                    v___y_2225_ = v___y_2286_;
                    v___y_2226_ = v___y_2279_;
                    v___y_2227_ = v___y_2284_;
                    v___y_2228_ = v___y_2285_;
                    v___y_2229_ = v___y_2282_;
                    v___y_2230_ = v___y_2275_;
                    v___y_2231_ = v___y_2277_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2281_);
                    crate::leanh::lean_dec(v___y_2276_);
                    crate::leanh::lean_dec_ref(v___x_2137_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    crate::leanh::lean_dec_ref(v___x_2131_);
                    crate::leanh::lean_del_object(v___x_2127_);
                    crate::leanh::lean_del_object(v___x_2120_);
                    crate::leanh::lean_dec(v_val_2118_);
                    crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2292_ = crate::leanh::lean_ctor_get(v___x_2291_, 0);
                    v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v___x_2291_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v___x_2294_ = v___x_2291_;
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2292_);
                        crate::leanh::lean_dec(v___x_2291_);
                        v___x_2294_ = crate::leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_2295_ == 0 {
                    v___x_2297_ = v___x_2294_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2297_;
            }
            26 => {
                crate::leanh::lean_inc_ref(v___x_2134_);
                crate::leanh::lean_inc_ref(v_type_2094_);
                crate::leanh::lean_inc(v_a_2107_);
                v___x_2311_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
                    v_a_2107_,
                    v_type_2094_,
                    v___x_2134_,
                    v___y_2301_,
                    v___y_2302_,
                    v___y_2303_,
                    v___y_2304_,
                    v___y_2305_,
                    v___y_2306_,
                    v___y_2307_,
                    v___y_2308_,
                    v___y_2309_,
                    v___y_2310_,
                );
                if crate::leanh::lean_obj_tag(v___x_2311_) == 0 {
                    v_a_2312_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    crate::leanh::lean_inc(v_a_2312_);
                    crate::leanh::lean_dec_ref_known(v___x_2311_, 1);
                    crate::leanh::lean_inc_ref(v_type_2094_);
                    crate::leanh::lean_inc(v_a_2107_);
                    v___x_2313_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
                        v_a_2107_,
                        v_type_2094_,
                        v___y_2307_,
                        v___y_2308_,
                        v___y_2309_,
                        v___y_2310_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2313_) == 0 {
                        v_a_2314_ = crate::leanh::lean_ctor_get(v___x_2313_, 0);
                        crate::leanh::lean_inc(v_a_2314_);
                        crate::leanh::lean_dec_ref_known(v___x_2313_, 1);
                        v_inheritedTraceOptions_2315_ =
                            crate::leanh::lean_ctor_get(v___y_2309_, 13);
                        v___x_2316_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_2123_, v_inheritedTraceOptions_2315_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
                        v_a_2317_ = crate::leanh::lean_ctor_get(v___x_2316_, 0);
                        crate::leanh::lean_inc(v_a_2317_);
                        crate::leanh::lean_dec_ref(v___x_2316_);
                        v___x_2318_ = (crate::leanh::lean_unbox(v_a_2317_) as u8);
                        crate::leanh::lean_dec(v_a_2317_);
                        if v___x_2318_ == 0 {
                            v___y_2220_ = v_a_2314_;
                            v___y_2221_ = v_a_2312_;
                            v___y_2222_ = v___y_2301_;
                            v___y_2223_ = v___y_2302_;
                            v___y_2224_ = v___y_2303_;
                            v___y_2225_ = v___y_2304_;
                            v___y_2226_ = v___y_2305_;
                            v___y_2227_ = v___y_2306_;
                            v___y_2228_ = v___y_2307_;
                            v___y_2229_ = v___y_2308_;
                            v___y_2230_ = v___y_2309_;
                            v___y_2231_ = v___y_2310_;
                            state = 16;
                            continue;
                        } else {
                            v___x_2319_ = l_Lean_Meta_Grind_updateLastTag(
                                v___y_2301_,
                                v___y_2302_,
                                v___y_2303_,
                                v___y_2304_,
                                v___y_2305_,
                                v___y_2306_,
                                v___y_2307_,
                                v___y_2308_,
                                v___y_2309_,
                                v___y_2310_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2319_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2319_, 1);
                                v___x_2320_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27);
                                if crate::leanh::lean_obj_tag(v_a_2314_) == 0 {
                                    v___x_2321_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24;
                                    v___y_2274_ = v___x_2320_;
                                    v___y_2275_ = v___y_2309_;
                                    v___y_2276_ = v_a_2314_;
                                    v___y_2277_ = v___y_2310_;
                                    v___y_2278_ = v___y_2301_;
                                    v___y_2279_ = v___y_2305_;
                                    v___y_2280_ = v___y_2303_;
                                    v___y_2281_ = v_a_2312_;
                                    v___y_2282_ = v___y_2308_;
                                    v___y_2283_ = v___y_2302_;
                                    v___y_2284_ = v___y_2306_;
                                    v___y_2285_ = v___y_2307_;
                                    v___y_2286_ = v___y_2304_;
                                    v___y_2287_ = v___x_2321_;
                                    state = 23;
                                    continue;
                                } else {
                                    v___x_2322_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25;
                                    v___y_2274_ = v___x_2320_;
                                    v___y_2275_ = v___y_2309_;
                                    v___y_2276_ = v_a_2314_;
                                    v___y_2277_ = v___y_2310_;
                                    v___y_2278_ = v___y_2301_;
                                    v___y_2279_ = v___y_2305_;
                                    v___y_2280_ = v___y_2303_;
                                    v___y_2281_ = v_a_2312_;
                                    v___y_2282_ = v___y_2308_;
                                    v___y_2283_ = v___y_2302_;
                                    v___y_2284_ = v___y_2306_;
                                    v___y_2285_ = v___y_2307_;
                                    v___y_2286_ = v___y_2304_;
                                    v___y_2287_ = v___x_2322_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2314_);
                                crate::leanh::lean_dec(v_a_2312_);
                                crate::leanh::lean_dec_ref(v___x_2137_);
                                crate::leanh::lean_dec_ref(v___x_2134_);
                                crate::leanh::lean_dec_ref(v___x_2131_);
                                crate::leanh::lean_del_object(v___x_2127_);
                                crate::leanh::lean_del_object(v___x_2120_);
                                crate::leanh::lean_dec(v_val_2118_);
                                crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                                crate::leanh::lean_dec(v_a_2107_);
                                crate::leanh::lean_dec_ref(v_type_2094_);
                                v_a_2323_ = crate::leanh::lean_ctor_get(v___x_2319_, 0);
                                v_isSharedCheck_2330_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2319_)) as u8;
                                if v_isSharedCheck_2330_ == 0 {
                                    v___x_2325_ = v___x_2319_;
                                    v_isShared_2326_ = v_isSharedCheck_2330_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2323_);
                                    crate::leanh::lean_dec(v___x_2319_);
                                    v___x_2325_ = crate::leanh::lean_box(0);
                                    v_isShared_2326_ = v_isSharedCheck_2330_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2312_);
                        crate::leanh::lean_dec_ref(v___x_2137_);
                        crate::leanh::lean_dec_ref(v___x_2134_);
                        crate::leanh::lean_dec_ref(v___x_2131_);
                        crate::leanh::lean_del_object(v___x_2127_);
                        crate::leanh::lean_del_object(v___x_2120_);
                        crate::leanh::lean_dec(v_val_2118_);
                        crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                        crate::leanh::lean_dec(v_a_2107_);
                        crate::leanh::lean_dec_ref(v_type_2094_);
                        v_a_2331_ = crate::leanh::lean_ctor_get(v___x_2313_, 0);
                        v_isSharedCheck_2338_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2313_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2313_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2331_);
                            crate::leanh::lean_dec(v___x_2313_);
                            v___x_2333_ = crate::leanh::lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2137_);
                    crate::leanh::lean_dec_ref(v___x_2134_);
                    crate::leanh::lean_dec_ref(v___x_2131_);
                    crate::leanh::lean_del_object(v___x_2127_);
                    crate::leanh::lean_del_object(v___x_2120_);
                    crate::leanh::lean_dec(v_val_2118_);
                    crate::leanh::lean_dec_ref_known(v___x_2110_, 2);
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec_ref(v_type_2094_);
                    v_a_2339_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2346_ = (!crate::leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2346_ == 0 {
                        v___x_2341_ = v___x_2311_;
                        v_isShared_2342_ = v_isSharedCheck_2346_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2339_);
                        crate::leanh::lean_dec(v___x_2311_);
                        v___x_2341_ = crate::leanh::lean_box(0);
                        v_isShared_2342_ = v_isSharedCheck_2346_;
                        state = 31;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2326_ == 0 {
                    v___x_2328_ = v___x_2325_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2328_;
            }
            29 => {
                if v_isShared_2334_ == 0 {
                    v___x_2336_ = v___x_2333_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2336_;
            }
            31 => {
                if v_isShared_2342_ == 0 {
                    v___x_2344_ = v___x_2341_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
                    v___x_2344_ = v_reuseFailAlloc_2345_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2344_;
            }
            33 => {
                if v_isShared_2356_ == 0 {
                    v___x_2358_ = v___x_2355_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2358_;
            }
            35 => {
                if v_isShared_2364_ == 0 {
                    v___x_2366_ = v___x_2363_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
                    v___x_2366_ = v_reuseFailAlloc_2367_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2366_;
            }
            37 => {
                return v___x_2373_;
            }
            38 => {
                if v_isShared_2379_ == 0 {
                    v___x_2381_ = v___x_2378_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
                    v___x_2381_ = v_reuseFailAlloc_2382_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2381_;
            }
            40 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(
    mut v_type_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2404_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
    crate::leanh::lean_dec(v_a_2402_);
    crate::leanh::lean_dec_ref(v_a_2401_);
    crate::leanh::lean_dec(v_a_2400_);
    crate::leanh::lean_dec_ref(v_a_2399_);
    crate::leanh::lean_dec(v_a_2398_);
    crate::leanh::lean_dec_ref(v_a_2397_);
    crate::leanh::lean_dec(v_a_2396_);
    crate::leanh::lean_dec_ref(v_a_2395_);
    crate::leanh::lean_dec(v_a_2394_);
    crate::leanh::lean_dec(v_a_2393_);
    return v_res_2404_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(
    mut v_cls_2405_: *mut crate::leanh::LeanObject,
    mut v_msg_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_2405_, v_msg_2406_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    return v___x_2418_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(
    mut v_cls_2419_: *mut crate::leanh::LeanObject,
    mut v_msg_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(v_cls_2419_, v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
    crate::leanh::lean_dec(v___y_2430_);
    crate::leanh::lean_dec_ref(v___y_2429_);
    crate::leanh::lean_dec(v___y_2428_);
    crate::leanh::lean_dec_ref(v___y_2427_);
    crate::leanh::lean_dec(v___y_2426_);
    crate::leanh::lean_dec_ref(v___y_2425_);
    crate::leanh::lean_dec(v___y_2424_);
    crate::leanh::lean_dec_ref(v___y_2423_);
    crate::leanh::lean_dec(v___y_2422_);
    crate::leanh::lean_dec(v___y_2421_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_2433_: *mut crate::leanh::LeanObject,
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v_x_2435_: *mut crate::leanh::LeanObject,
    mut v_x_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2437_ = crate::leanh::lean_ctor_get(v_x_2433_, 0);
                v_vs_2438_ = crate::leanh::lean_ctor_get(v_x_2433_, 1);
                v_isSharedCheck_2462_ = (!crate::leanh::lean_is_exclusive(v_x_2433_)) as u8;
                if v_isSharedCheck_2462_ == 0 {
                    v___x_2440_ = v_x_2433_;
                    v_isShared_2441_ = v_isSharedCheck_2462_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2438_);
                    crate::leanh::lean_inc(v_ks_2437_);
                    crate::leanh::lean_dec(v_x_2433_);
                    v___x_2440_ = crate::leanh::lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2462_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2442_ = lean_array_get_size(v_ks_2437_);
                v___x_2443_ = lean_nat_dec_lt(v_x_2434_, v___x_2442_);
                if v___x_2443_ == 0 {
                    crate::leanh::lean_dec(v_x_2434_);
                    v___x_2444_ = lean_array_push(v_ks_2437_, v_x_2435_);
                    v___x_2445_ = lean_array_push(v_vs_2438_, v_x_2436_);
                    if v_isShared_2441_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2440_, 1, v___x_2445_);
                        crate::leanh::lean_ctor_set(v___x_2440_, 0, v___x_2444_);
                        v___x_2447_ = v___x_2440_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2444_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2445_);
                        v___x_2447_ = v_reuseFailAlloc_2448_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2449_ = lean_array_fget_borrowed(v_ks_2437_, v_x_2434_);
                    v___x_2450_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_2435_,
                            v_k_x27_2449_,
                        );
                    if v___x_2450_ == 0 {
                        if v_isShared_2441_ == 0 {
                            v___x_2452_ = v___x_2440_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2456_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_ks_2437_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_vs_2438_);
                            v___x_2452_ = v_reuseFailAlloc_2456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2457_ = lean_array_fset(v_ks_2437_, v_x_2434_, v_x_2435_);
                        v___x_2458_ = lean_array_fset(v_vs_2438_, v_x_2434_, v_x_2436_);
                        crate::leanh::lean_dec(v_x_2434_);
                        if v_isShared_2441_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2440_, 1, v___x_2458_);
                            crate::leanh::lean_ctor_set(v___x_2440_, 0, v___x_2457_);
                            v___x_2460_ = v___x_2440_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2461_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2457_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2458_);
                            v___x_2460_ = v_reuseFailAlloc_2461_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2447_;
            }
            3 => {
                v___x_2453_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2454_ = lean_nat_add(v_x_2434_, v___x_2453_);
                crate::leanh::lean_dec(v_x_2434_);
                v_x_2433_ = v___x_2452_;
                v_x_2434_ = v___x_2454_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_2463_: *mut crate::leanh::LeanObject,
    mut v_k_2464_: *mut crate::leanh::LeanObject,
    mut v_v_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2467_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2463_, v___x_2466_, v_k_2464_, v_v_2465_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2468_: usize = 0;
    let mut v___x_2469_: usize = 0;
    let mut v___x_2470_: usize = 0;
    v___x_2468_ = 5usize;
    v___x_2469_ = 1usize;
    v___x_2470_ = lean_usize_shift_left(v___x_2469_, v___x_2468_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: usize = 0;
    let mut v___x_2473_: usize = 0;
    v___x_2471_ = 1usize;
    v___x_2472_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_2473_ = lean_usize_sub(v___x_2472_, v___x_2471_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2474_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v_x_2476_: usize,
    mut v_x_2477_: usize,
    mut v_x_2478_: *mut crate::leanh::LeanObject,
    mut v_x_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: usize = 0;
    let mut v___x_2482_: usize = 0;
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v_j_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v_v_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_node_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2516_: usize = 0;
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2524_: u8 = 0;
    let mut v_unused_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: u8 = 0;
    let mut v_ks_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: usize = 0;
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v_reuseFailAlloc_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2475_) == 0 {
                    v_es_2480_ = crate::leanh::lean_ctor_get(v_x_2475_, 0);
                    v___x_2481_ = 5usize;
                    v___x_2482_ = 1usize;
                    v___x_2483_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2484_ = lean_usize_land(v_x_2476_, v___x_2483_);
                    v_j_2485_ = lean_usize_to_nat(v___x_2484_);
                    v___x_2486_ = lean_array_get_size(v_es_2480_);
                    v___x_2487_ = lean_nat_dec_lt(v_j_2485_, v___x_2486_);
                    if v___x_2487_ == 0 {
                        crate::leanh::lean_dec(v_j_2485_);
                        crate::leanh::lean_dec(v_x_2479_);
                        crate::leanh::lean_dec_ref(v_x_2478_);
                        return v_x_2475_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2480_);
                        v_isSharedCheck_2524_ = (!crate::leanh::lean_is_exclusive(v_x_2475_)) as u8;
                        if v_isSharedCheck_2524_ == 0 {
                            v_unused_2525_ = crate::leanh::lean_ctor_get(v_x_2475_, 0);
                            crate::leanh::lean_dec(v_unused_2525_);
                            v___x_2489_ = v_x_2475_;
                            v_isShared_2490_ = v_isSharedCheck_2524_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2475_);
                            v___x_2489_ = crate::leanh::lean_box(0);
                            v_isShared_2490_ = v_isSharedCheck_2524_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2526_ = crate::leanh::lean_ctor_get(v_x_2475_, 0);
                    v_vs_2527_ = crate::leanh::lean_ctor_get(v_x_2475_, 1);
                    v_isSharedCheck_2547_ = (!crate::leanh::lean_is_exclusive(v_x_2475_)) as u8;
                    if v_isSharedCheck_2547_ == 0 {
                        v___x_2529_ = v_x_2475_;
                        v_isShared_2530_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2527_);
                        crate::leanh::lean_inc(v_ks_2526_);
                        crate::leanh::lean_dec(v_x_2475_);
                        v___x_2529_ = crate::leanh::lean_box(0);
                        v_isShared_2530_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2491_ = lean_array_fget(v_es_2480_, v_j_2485_);
                v___x_2492_ = crate::leanh::lean_box(0);
                v_xs_x27_2493_ = lean_array_fset(v_es_2480_, v_j_2485_, v___x_2492_);
                match crate::leanh::lean_obj_tag(v_v_2491_) {
                    0 => {
                        v_key_2500_ = crate::leanh::lean_ctor_get(v_v_2491_, 0);
                        v_val_2501_ = crate::leanh::lean_ctor_get(v_v_2491_, 1);
                        v_isSharedCheck_2511_ = (!crate::leanh::lean_is_exclusive(v_v_2491_)) as u8;
                        if v_isSharedCheck_2511_ == 0 {
                            v___x_2503_ = v_v_2491_;
                            v_isShared_2504_ = v_isSharedCheck_2511_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2501_);
                            crate::leanh::lean_inc(v_key_2500_);
                            crate::leanh::lean_dec(v_v_2491_);
                            v___x_2503_ = crate::leanh::lean_box(0);
                            v_isShared_2504_ = v_isSharedCheck_2511_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2512_ = crate::leanh::lean_ctor_get(v_v_2491_, 0);
                        v_isSharedCheck_2522_ = (!crate::leanh::lean_is_exclusive(v_v_2491_)) as u8;
                        if v_isSharedCheck_2522_ == 0 {
                            v___x_2514_ = v_v_2491_;
                            v_isShared_2515_ = v_isSharedCheck_2522_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2512_);
                            crate::leanh::lean_dec(v_v_2491_);
                            v___x_2514_ = crate::leanh::lean_box(0);
                            v_isShared_2515_ = v_isSharedCheck_2522_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2523_, 0, v_x_2478_);
                        crate::leanh::lean_ctor_set(v___x_2523_, 1, v_x_2479_);
                        v___y_2495_ = v___x_2523_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2496_ = lean_array_fset(v_xs_x27_2493_, v_j_2485_, v___y_2495_);
                crate::leanh::lean_dec(v_j_2485_);
                if v_isShared_2490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2489_, 0, v___x_2496_);
                    v___x_2498_ = v___x_2489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2498_;
            }
            4 => {
                v___x_2505_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_2478_,
                        v_key_2500_,
                    );
                if v___x_2505_ == 0 {
                    crate::leanh::lean_del_object(v___x_2503_);
                    v___x_2506_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2500_,
                        v_val_2501_,
                        v_x_2478_,
                        v_x_2479_,
                    );
                    v___x_2507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2507_, 0, v___x_2506_);
                    v___y_2495_ = v___x_2507_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2501_);
                    crate::leanh::lean_dec(v_key_2500_);
                    if v_isShared_2504_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2503_, 1, v_x_2479_);
                        crate::leanh::lean_ctor_set(v___x_2503_, 0, v_x_2478_);
                        v___x_2509_ = v___x_2503_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_x_2478_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_x_2479_);
                        v___x_2509_ = v_reuseFailAlloc_2510_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2495_ = v___x_2509_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2516_ = lean_usize_shift_right(v_x_2476_, v___x_2481_);
                v___x_2517_ = lean_usize_add(v_x_2477_, v___x_2482_);
                v___x_2518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_2512_, v___x_2516_, v___x_2517_, v_x_2478_, v_x_2479_);
                if v_isShared_2515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2514_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2495_ = v___x_2520_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2530_ == 0 {
                    v___x_2532_ = v___x_2529_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_ks_2526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_vs_2527_);
                    v___x_2532_ = v_reuseFailAlloc_2546_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2533_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_2532_, v_x_2478_, v_x_2479_);
                v___x_2541_ = 7usize;
                v___x_2542_ = lean_usize_dec_le(v___x_2541_, v_x_2477_);
                if v___x_2542_ == 0 {
                    v___x_2543_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2533_);
                    v___x_2544_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2545_ = lean_nat_dec_lt(v___x_2543_, v___x_2544_);
                    crate::leanh::lean_dec(v___x_2543_);
                    v___y_2535_ = v___x_2545_;
                    state = 10;
                    continue;
                } else {
                    v___y_2535_ = v___x_2542_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2535_ == 0 {
                    v_ks_2536_ = crate::leanh::lean_ctor_get(v_newNode_2533_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2536_);
                    v_vs_2537_ = crate::leanh::lean_ctor_get(v_newNode_2533_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2537_);
                    crate::leanh::lean_dec_ref(v_newNode_2533_);
                    v___x_2538_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_2540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_2477_, v_ks_2536_, v_vs_2537_, v___x_2538_, v___x_2539_);
                    crate::leanh::lean_dec_ref(v_vs_2537_);
                    crate::leanh::lean_dec_ref(v_ks_2536_);
                    return v___x_2540_;
                } else {
                    return v_newNode_2533_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_2548_: usize,
    mut v_keys_2549_: *mut crate::leanh::LeanObject,
    mut v_vals_2550_: *mut crate::leanh::LeanObject,
    mut v_i_2551_: *mut crate::leanh::LeanObject,
    mut v_entries_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v_k_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: u64 = 0;
    let mut v_h_2558_: usize = 0;
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v_h_2564_: usize = 0;
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2553_ = lean_array_get_size(v_keys_2549_);
                v___x_2554_ = lean_nat_dec_lt(v_i_2551_, v___x_2553_);
                if v___x_2554_ == 0 {
                    crate::leanh::lean_dec(v_i_2551_);
                    return v_entries_2552_;
                } else {
                    v_k_2555_ = lean_array_fget_borrowed(v_keys_2549_, v_i_2551_);
                    v_v_2556_ = lean_array_fget_borrowed(v_vals_2550_, v_i_2551_);
                    v___x_2557_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2555_);
                    v_h_2558_ = lean_uint64_to_usize(v___x_2557_);
                    v___x_2559_ = 5usize;
                    v___x_2560_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2561_ = 1usize;
                    v___x_2562_ = lean_usize_sub(v_depth_2548_, v___x_2561_);
                    v___x_2563_ = lean_usize_mul(v___x_2559_, v___x_2562_);
                    v_h_2564_ = lean_usize_shift_right(v_h_2558_, v___x_2563_);
                    v___x_2565_ = lean_nat_add(v_i_2551_, v___x_2560_);
                    crate::leanh::lean_dec(v_i_2551_);
                    crate::leanh::lean_inc(v_v_2556_);
                    crate::leanh::lean_inc(v_k_2555_);
                    v___x_2566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_2552_, v_h_2564_, v_depth_2548_, v_k_2555_, v_v_2556_);
                    v_i_2551_ = v___x_2565_;
                    v_entries_2552_ = v___x_2566_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_2568_: *mut crate::leanh::LeanObject,
    mut v_keys_2569_: *mut crate::leanh::LeanObject,
    mut v_vals_2570_: *mut crate::leanh::LeanObject,
    mut v_i_2571_: *mut crate::leanh::LeanObject,
    mut v_entries_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2573_: usize = 0;
    let mut v_res_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2573_ = crate::leanh::lean_unbox_usize(v_depth_2568_);
    crate::leanh::lean_dec(v_depth_2568_);
    v_res_2574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2573_, v_keys_2569_, v_vals_2570_, v_i_2571_, v_entries_2572_);
    crate::leanh::lean_dec_ref(v_vals_2570_);
    crate::leanh::lean_dec_ref(v_keys_2569_);
    return v_res_2574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_2575_: *mut crate::leanh::LeanObject,
    mut v_x_2576_: *mut crate::leanh::LeanObject,
    mut v_x_2577_: *mut crate::leanh::LeanObject,
    mut v_x_2578_: *mut crate::leanh::LeanObject,
    mut v_x_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3692__boxed_2580_: usize = 0;
    let mut v_x_3693__boxed_2581_: usize = 0;
    let mut v_res_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3692__boxed_2580_ = crate::leanh::lean_unbox_usize(v_x_2576_);
    crate::leanh::lean_dec(v_x_2576_);
    v_x_3693__boxed_2581_ = crate::leanh::lean_unbox_usize(v_x_2577_);
    crate::leanh::lean_dec(v_x_2577_);
    v_res_2582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2575_, v_x_3692__boxed_2580_, v_x_3693__boxed_2581_, v_x_2578_, v_x_2579_);
    return v_res_2582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(
    mut v_x_2583_: *mut crate::leanh::LeanObject,
    mut v_x_2584_: *mut crate::leanh::LeanObject,
    mut v_x_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2584_);
    v___x_2587_ = lean_uint64_to_usize(v___x_2586_);
    v___x_2588_ = 1usize;
    v___x_2589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2583_, v___x_2587_, v___x_2588_, v_x_2584_, v_x_2585_);
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(
    mut v_type_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_s_2592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2606_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2593_ = crate::leanh::lean_ctor_get(v_s_2592_, 0);
                v_typeIdOf_2594_ = crate::leanh::lean_ctor_get(v_s_2592_, 1);
                v_exprToRingId_2595_ = crate::leanh::lean_ctor_get(v_s_2592_, 2);
                v_semirings_2596_ = crate::leanh::lean_ctor_get(v_s_2592_, 3);
                v_stypeIdOf_2597_ = crate::leanh::lean_ctor_get(v_s_2592_, 4);
                v_exprToSemiringId_2598_ = crate::leanh::lean_ctor_get(v_s_2592_, 5);
                v_ncRings_2599_ = crate::leanh::lean_ctor_get(v_s_2592_, 6);
                v_exprToNCRingId_2600_ = crate::leanh::lean_ctor_get(v_s_2592_, 7);
                v_nctypeIdOf_2601_ = crate::leanh::lean_ctor_get(v_s_2592_, 8);
                v_ncSemirings_2602_ = crate::leanh::lean_ctor_get(v_s_2592_, 9);
                v_exprToNCSemiringId_2603_ = crate::leanh::lean_ctor_get(v_s_2592_, 10);
                v_ncstypeIdOf_2604_ = crate::leanh::lean_ctor_get(v_s_2592_, 11);
                v_steps_2605_ = crate::leanh::lean_ctor_get(v_s_2592_, 12);
                v_reportedMaxDegreeIssue_2606_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2592_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2614_ = (!crate::leanh::lean_is_exclusive(v_s_2592_)) as u8;
                if v_isSharedCheck_2614_ == 0 {
                    v___x_2608_ = v_s_2592_;
                    v_isShared_2609_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_2605_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_2604_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_2603_);
                    crate::leanh::lean_inc(v_ncSemirings_2602_);
                    crate::leanh::lean_inc(v_nctypeIdOf_2601_);
                    crate::leanh::lean_inc(v_exprToNCRingId_2600_);
                    crate::leanh::lean_inc(v_ncRings_2599_);
                    crate::leanh::lean_inc(v_exprToSemiringId_2598_);
                    crate::leanh::lean_inc(v_stypeIdOf_2597_);
                    crate::leanh::lean_inc(v_semirings_2596_);
                    crate::leanh::lean_inc(v_exprToRingId_2595_);
                    crate::leanh::lean_inc(v_typeIdOf_2594_);
                    crate::leanh::lean_inc(v_rings_2593_);
                    crate::leanh::lean_dec(v_s_2592_);
                    v___x_2608_ = crate::leanh::lean_box(0);
                    v_isShared_2609_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2610_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_2594_, v_type_2590_, v_a_2591_);
                if v_isShared_2609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2608_, 1, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_rings_2593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_exprToRingId_2595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_semirings_2596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_stypeIdOf_2597_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2613_,
                        5,
                        v_exprToSemiringId_2598_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_ncRings_2599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_exprToNCRingId_2600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_nctypeIdOf_2601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 9, v_ncSemirings_2602_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2613_,
                        10,
                        v_exprToNCSemiringId_2603_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 11, v_ncstypeIdOf_2604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 12, v_steps_2605_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2613_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_2606_,
                    );
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2615_: *mut crate::leanh::LeanObject,
    mut v_vals_2616_: *mut crate::leanh::LeanObject,
    mut v_i_2617_: *mut crate::leanh::LeanObject,
    mut v_k_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: u8 = 0;
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2619_ = lean_array_get_size(v_keys_2615_);
                v___x_2620_ = lean_nat_dec_lt(v_i_2617_, v___x_2619_);
                if v___x_2620_ == 0 {
                    crate::leanh::lean_dec(v_i_2617_);
                    v___x_2621_ = crate::leanh::lean_box(0);
                    return v___x_2621_;
                } else {
                    v_k_x27_2622_ = lean_array_fget_borrowed(v_keys_2615_, v_i_2617_);
                    v___x_2623_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2618_,
                            v_k_x27_2622_,
                        );
                    if v___x_2623_ == 0 {
                        v___x_2624_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2625_ = lean_nat_add(v_i_2617_, v___x_2624_);
                        crate::leanh::lean_dec(v_i_2617_);
                        v_i_2617_ = v___x_2625_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2627_ = lean_array_fget_borrowed(v_vals_2616_, v_i_2617_);
                        crate::leanh::lean_dec(v_i_2617_);
                        crate::leanh::lean_inc(v___x_2627_);
                        v___x_2628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2628_, 0, v___x_2627_);
                        return v___x_2628_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2629_: *mut crate::leanh::LeanObject,
    mut v_vals_2630_: *mut crate::leanh::LeanObject,
    mut v_i_2631_: *mut crate::leanh::LeanObject,
    mut v_k_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2633_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2629_, v_vals_2630_, v_i_2631_, v_k_2632_);
    crate::leanh::lean_dec_ref(v_k_2632_);
    crate::leanh::lean_dec_ref(v_vals_2630_);
    crate::leanh::lean_dec_ref(v_keys_2629_);
    return v_res_2633_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(
    mut v_x_2634_: *mut crate::leanh::LeanObject,
    mut v_x_2635_: usize,
    mut v_x_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: usize = 0;
    let mut v_j_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: usize = 0;
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2634_) == 0 {
                    v_es_2637_ = crate::leanh::lean_ctor_get(v_x_2634_, 0);
                    v___x_2638_ = crate::leanh::lean_box(2);
                    v___x_2639_ = 5usize;
                    v___x_2640_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2641_ = lean_usize_land(v_x_2635_, v___x_2640_);
                    v_j_2642_ = lean_usize_to_nat(v___x_2641_);
                    v___x_2643_ = lean_array_get_borrowed(v___x_2638_, v_es_2637_, v_j_2642_);
                    crate::leanh::lean_dec(v_j_2642_);
                    match crate::leanh::lean_obj_tag(v___x_2643_) {
                        0 => {
                            v_key_2644_ = crate::leanh::lean_ctor_get(v___x_2643_, 0);
                            v_val_2645_ = crate::leanh::lean_ctor_get(v___x_2643_, 1);
                            v___x_2646_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2636_, v_key_2644_);
                            if v___x_2646_ == 0 {
                                v___x_2647_ = crate::leanh::lean_box(0);
                                return v___x_2647_;
                            } else {
                                crate::leanh::lean_inc(v_val_2645_);
                                v___x_2648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2648_, 0, v_val_2645_);
                                return v___x_2648_;
                            }
                        }
                        1 => {
                            v_node_2649_ = crate::leanh::lean_ctor_get(v___x_2643_, 0);
                            v___x_2650_ = lean_usize_shift_right(v_x_2635_, v___x_2639_);
                            v_x_2634_ = v_node_2649_;
                            v_x_2635_ = v___x_2650_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2652_ = crate::leanh::lean_box(0);
                            return v___x_2652_;
                        }
                    }
                } else {
                    v_ks_2653_ = crate::leanh::lean_ctor_get(v_x_2634_, 0);
                    v_vs_2654_ = crate::leanh::lean_ctor_get(v_x_2634_, 1);
                    v___x_2655_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2656_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2653_, v_vs_2654_, v___x_2655_, v_x_2636_);
                    return v___x_2656_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2657_: *mut crate::leanh::LeanObject,
    mut v_x_2658_: *mut crate::leanh::LeanObject,
    mut v_x_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3910__boxed_2660_: usize = 0;
    let mut v_res_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3910__boxed_2660_ = crate::leanh::lean_unbox_usize(v_x_2658_);
    crate::leanh::lean_dec(v_x_2658_);
    v_res_2661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2657_, v_x_3910__boxed_2660_, v_x_2659_);
    crate::leanh::lean_dec_ref(v_x_2659_);
    crate::leanh::lean_dec_ref(v_x_2657_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(
    mut v_x_2662_: *mut crate::leanh::LeanObject,
    mut v_x_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2664_: u64 = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2663_);
    v___x_2665_ = lean_uint64_to_usize(v___x_2664_);
    v___x_2666_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2662_, v___x_2665_, v_x_2663_);
    return v___x_2666_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(
    mut v_x_2667_: *mut crate::leanh::LeanObject,
    mut v_x_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_2667_, v_x_2668_);
    crate::leanh::lean_dec_ref(v_x_2668_);
    crate::leanh::lean_dec_ref(v_x_2667_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
    mut v_type_2670_: *mut crate::leanh::LeanObject,
    mut v_a_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_a_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v_typeIdOf_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_unused_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
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
                v___x_2682_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2671_, v_a_2679_);
                if crate::leanh::lean_obj_tag(v___x_2682_) == 0 {
                    v_a_2683_ = crate::leanh::lean_ctor_get(v___x_2682_, 0);
                    v_isSharedCheck_2714_ = (!crate::leanh::lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2714_ == 0 {
                        v___x_2685_ = v___x_2682_;
                        v_isShared_2686_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2683_);
                        crate::leanh::lean_dec(v___x_2682_);
                        v___x_2685_ = crate::leanh::lean_box(0);
                        v_isShared_2686_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2670_);
                    v_a_2715_ = crate::leanh::lean_ctor_get(v___x_2682_, 0);
                    v_isSharedCheck_2722_ = (!crate::leanh::lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v___x_2717_ = v___x_2682_;
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2715_);
                        crate::leanh::lean_dec(v___x_2682_);
                        v___x_2717_ = crate::leanh::lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_typeIdOf_2687_ = crate::leanh::lean_ctor_get(v_a_2683_, 1);
                crate::leanh::lean_inc_ref(v_typeIdOf_2687_);
                crate::leanh::lean_dec(v_a_2683_);
                v___x_2688_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_2687_, v_type_2670_);
                crate::leanh::lean_dec_ref(v_typeIdOf_2687_);
                if crate::leanh::lean_obj_tag(v___x_2688_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2670_);
                    v_val_2689_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                    crate::leanh::lean_inc(v_val_2689_);
                    crate::leanh::lean_dec_ref_known(v___x_2688_, 1);
                    if v_isShared_2686_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2685_, 0, v_val_2689_);
                        v___x_2691_ = v___x_2685_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_val_2689_);
                        v___x_2691_ = v_reuseFailAlloc_2692_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2688_);
                    crate::leanh::lean_del_object(v___x_2685_);
                    crate::leanh::lean_inc_ref(v_type_2670_);
                    v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
                    if crate::leanh::lean_obj_tag(v___x_2693_) == 0 {
                        v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                        crate::leanh::lean_inc_n(v_a_2694_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2693_, 1);
                        v___f_2695_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_2695_, 0, v_type_2670_);
                        crate::leanh::lean_closure_set(v___f_2695_, 1, v_a_2694_);
                        v___x_2696_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_2697_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2696_, v___f_2695_, v_a_2671_);
                        if crate::leanh::lean_obj_tag(v___x_2697_) == 0 {
                            v_isSharedCheck_2704_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2697_)) as u8;
                            if v_isSharedCheck_2704_ == 0 {
                                v_unused_2705_ = crate::leanh::lean_ctor_get(v___x_2697_, 0);
                                crate::leanh::lean_dec(v_unused_2705_);
                                v___x_2699_ = v___x_2697_;
                                v_isShared_2700_ = v_isSharedCheck_2704_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2697_);
                                v___x_2699_ = crate::leanh::lean_box(0);
                                v_isShared_2700_ = v_isSharedCheck_2704_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2694_);
                            v_a_2706_ = crate::leanh::lean_ctor_get(v___x_2697_, 0);
                            v_isSharedCheck_2713_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2697_)) as u8;
                            if v_isSharedCheck_2713_ == 0 {
                                v___x_2708_ = v___x_2697_;
                                v_isShared_2709_ = v_isSharedCheck_2713_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2706_);
                                crate::leanh::lean_dec(v___x_2697_);
                                v___x_2708_ = crate::leanh::lean_box(0);
                                v_isShared_2709_ = v_isSharedCheck_2713_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_2670_);
                        return v___x_2693_;
                    }
                }
            }
            2 => {
                return v___x_2691_;
            }
            3 => {
                if v_isShared_2700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2699_, 0, v_a_2694_);
                    v___x_2702_ = v___x_2699_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2694_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2702_;
            }
            5 => {
                if v_isShared_2709_ == 0 {
                    v___x_2711_ = v___x_2708_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2711_;
            }
            7 => {
                if v_isShared_2718_ == 0 {
                    v___x_2720_ = v___x_2717_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
                    v___x_2720_ = v_reuseFailAlloc_2721_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(
    mut v_type_2723_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
        v_type_2723_,
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
    );
    crate::leanh::lean_dec(v_a_2733_);
    crate::leanh::lean_dec_ref(v_a_2732_);
    crate::leanh::lean_dec(v_a_2731_);
    crate::leanh::lean_dec_ref(v_a_2730_);
    crate::leanh::lean_dec(v_a_2729_);
    crate::leanh::lean_dec_ref(v_a_2728_);
    crate::leanh::lean_dec(v_a_2727_);
    crate::leanh::lean_dec_ref(v_a_2726_);
    crate::leanh::lean_dec(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    return v_res_2735_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(
    mut v_00_u03b2_2736_: *mut crate::leanh::LeanObject,
    mut v_x_2737_: *mut crate::leanh::LeanObject,
    mut v_x_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_2737_, v_x_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(
    mut v_00_u03b2_2740_: *mut crate::leanh::LeanObject,
    mut v_x_2741_: *mut crate::leanh::LeanObject,
    mut v_x_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2743_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_2740_, v_x_2741_, v_x_2742_);
    crate::leanh::lean_dec_ref(v_x_2742_);
    crate::leanh::lean_dec_ref(v_x_2741_);
    return v_res_2743_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(
    mut v_00_u03b2_2744_: *mut crate::leanh::LeanObject,
    mut v_x_2745_: *mut crate::leanh::LeanObject,
    mut v_x_2746_: *mut crate::leanh::LeanObject,
    mut v_x_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_2745_, v_x_2746_, v_x_2747_);
    return v___x_2748_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(
    mut v_00_u03b2_2749_: *mut crate::leanh::LeanObject,
    mut v_x_2750_: *mut crate::leanh::LeanObject,
    mut v_x_2751_: usize,
    mut v_x_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2750_, v_x_2751_, v_x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2754_: *mut crate::leanh::LeanObject,
    mut v_x_2755_: *mut crate::leanh::LeanObject,
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4072__boxed_2758_: usize = 0;
    let mut v_res_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4072__boxed_2758_ = crate::leanh::lean_unbox_usize(v_x_2756_);
    crate::leanh::lean_dec(v_x_2756_);
    v_res_2759_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_2754_, v_x_2755_, v_x_4072__boxed_2758_, v_x_2757_);
    crate::leanh::lean_dec_ref(v_x_2757_);
    crate::leanh::lean_dec_ref(v_x_2755_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(
    mut v_00_u03b2_2760_: *mut crate::leanh::LeanObject,
    mut v_x_2761_: *mut crate::leanh::LeanObject,
    mut v_x_2762_: usize,
    mut v_x_2763_: usize,
    mut v_x_2764_: *mut crate::leanh::LeanObject,
    mut v_x_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2761_, v_x_2762_, v_x_2763_, v_x_2764_, v_x_2765_);
    return v___x_2766_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2767_: *mut crate::leanh::LeanObject,
    mut v_x_2768_: *mut crate::leanh::LeanObject,
    mut v_x_2769_: *mut crate::leanh::LeanObject,
    mut v_x_2770_: *mut crate::leanh::LeanObject,
    mut v_x_2771_: *mut crate::leanh::LeanObject,
    mut v_x_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4083__boxed_2773_: usize = 0;
    let mut v_x_4084__boxed_2774_: usize = 0;
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4083__boxed_2773_ = crate::leanh::lean_unbox_usize(v_x_2769_);
    crate::leanh::lean_dec(v_x_2769_);
    v_x_4084__boxed_2774_ = crate::leanh::lean_unbox_usize(v_x_2770_);
    crate::leanh::lean_dec(v_x_2770_);
    v_res_2775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_2767_, v_x_2768_, v_x_4083__boxed_2773_, v_x_4084__boxed_2774_, v_x_2771_, v_x_2772_);
    return v_res_2775_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2776_: *mut crate::leanh::LeanObject,
    mut v_keys_2777_: *mut crate::leanh::LeanObject,
    mut v_vals_2778_: *mut crate::leanh::LeanObject,
    mut v_heq_2779_: *mut crate::leanh::LeanObject,
    mut v_i_2780_: *mut crate::leanh::LeanObject,
    mut v_k_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2777_, v_vals_2778_, v_i_2780_, v_k_2781_);
    return v___x_2782_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2783_: *mut crate::leanh::LeanObject,
    mut v_keys_2784_: *mut crate::leanh::LeanObject,
    mut v_vals_2785_: *mut crate::leanh::LeanObject,
    mut v_heq_2786_: *mut crate::leanh::LeanObject,
    mut v_i_2787_: *mut crate::leanh::LeanObject,
    mut v_k_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2783_, v_keys_2784_, v_vals_2785_, v_heq_2786_, v_i_2787_, v_k_2788_);
    crate::leanh::lean_dec_ref(v_k_2788_);
    crate::leanh::lean_dec_ref(v_vals_2785_);
    crate::leanh::lean_dec_ref(v_keys_2784_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2790_: *mut crate::leanh::LeanObject,
    mut v_n_2791_: *mut crate::leanh::LeanObject,
    mut v_k_2792_: *mut crate::leanh::LeanObject,
    mut v_v_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_2791_, v_k_2792_, v_v_2793_);
    return v___x_2794_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2795_: *mut crate::leanh::LeanObject,
    mut v_depth_2796_: usize,
    mut v_keys_2797_: *mut crate::leanh::LeanObject,
    mut v_vals_2798_: *mut crate::leanh::LeanObject,
    mut v_heq_2799_: *mut crate::leanh::LeanObject,
    mut v_i_2800_: *mut crate::leanh::LeanObject,
    mut v_entries_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2796_, v_keys_2797_, v_vals_2798_, v_i_2800_, v_entries_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2803_: *mut crate::leanh::LeanObject,
    mut v_depth_2804_: *mut crate::leanh::LeanObject,
    mut v_keys_2805_: *mut crate::leanh::LeanObject,
    mut v_vals_2806_: *mut crate::leanh::LeanObject,
    mut v_heq_2807_: *mut crate::leanh::LeanObject,
    mut v_i_2808_: *mut crate::leanh::LeanObject,
    mut v_entries_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2810_: usize = 0;
    let mut v_res_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2810_ = crate::leanh::lean_unbox_usize(v_depth_2804_);
    crate::leanh::lean_dec(v_depth_2804_);
    v_res_2811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2803_, v_depth_boxed_2810_, v_keys_2805_, v_vals_2806_, v_heq_2807_, v_i_2808_, v_entries_2809_);
    crate::leanh::lean_dec_ref(v_vals_2806_);
    crate::leanh::lean_dec_ref(v_keys_2805_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2812_: *mut crate::leanh::LeanObject,
    mut v_x_2813_: *mut crate::leanh::LeanObject,
    mut v_x_2814_: *mut crate::leanh::LeanObject,
    mut v_x_2815_: *mut crate::leanh::LeanObject,
    mut v_x_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2813_, v_x_2814_, v_x_2815_, v_x_2816_);
    return v___x_2817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(
    mut v___x_2818_: *mut crate::leanh::LeanObject,
    mut v_s_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2833_: u8 = 0;
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2820_ = crate::leanh::lean_ctor_get(v_s_2819_, 0);
                v_typeIdOf_2821_ = crate::leanh::lean_ctor_get(v_s_2819_, 1);
                v_exprToRingId_2822_ = crate::leanh::lean_ctor_get(v_s_2819_, 2);
                v_semirings_2823_ = crate::leanh::lean_ctor_get(v_s_2819_, 3);
                v_stypeIdOf_2824_ = crate::leanh::lean_ctor_get(v_s_2819_, 4);
                v_exprToSemiringId_2825_ = crate::leanh::lean_ctor_get(v_s_2819_, 5);
                v_ncRings_2826_ = crate::leanh::lean_ctor_get(v_s_2819_, 6);
                v_exprToNCRingId_2827_ = crate::leanh::lean_ctor_get(v_s_2819_, 7);
                v_nctypeIdOf_2828_ = crate::leanh::lean_ctor_get(v_s_2819_, 8);
                v_ncSemirings_2829_ = crate::leanh::lean_ctor_get(v_s_2819_, 9);
                v_exprToNCSemiringId_2830_ = crate::leanh::lean_ctor_get(v_s_2819_, 10);
                v_ncstypeIdOf_2831_ = crate::leanh::lean_ctor_get(v_s_2819_, 11);
                v_steps_2832_ = crate::leanh::lean_ctor_get(v_s_2819_, 12);
                v_reportedMaxDegreeIssue_2833_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2819_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2841_ = (!crate::leanh::lean_is_exclusive(v_s_2819_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v___x_2835_ = v_s_2819_;
                    v_isShared_2836_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_2832_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_2831_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_2830_);
                    crate::leanh::lean_inc(v_ncSemirings_2829_);
                    crate::leanh::lean_inc(v_nctypeIdOf_2828_);
                    crate::leanh::lean_inc(v_exprToNCRingId_2827_);
                    crate::leanh::lean_inc(v_ncRings_2826_);
                    crate::leanh::lean_inc(v_exprToSemiringId_2825_);
                    crate::leanh::lean_inc(v_stypeIdOf_2824_);
                    crate::leanh::lean_inc(v_semirings_2823_);
                    crate::leanh::lean_inc(v_exprToRingId_2822_);
                    crate::leanh::lean_inc(v_typeIdOf_2821_);
                    crate::leanh::lean_inc(v_rings_2820_);
                    crate::leanh::lean_dec(v_s_2819_);
                    v___x_2835_ = crate::leanh::lean_box(0);
                    v_isShared_2836_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2837_ = lean_array_push(v_ncRings_2826_, v___x_2818_);
                if v_isShared_2836_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2835_, 6, v___x_2837_);
                    v___x_2839_ = v___x_2835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_rings_2820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_typeIdOf_2821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_exprToRingId_2822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_semirings_2823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_stypeIdOf_2824_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2840_,
                        5,
                        v_exprToSemiringId_2825_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 6, v___x_2837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_exprToNCRingId_2827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 8, v_nctypeIdOf_2828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 9, v_ncSemirings_2829_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2840_,
                        10,
                        v_exprToNCSemiringId_2830_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 11, v_ncstypeIdOf_2831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 12, v_steps_2832_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_2833_,
                    );
                    v___x_2839_ = v_reuseFailAlloc_2840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(
    mut v_type_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
    mut v_a_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v_options_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v_inheritedTraceOptions_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2876_: u8 = 0;
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2906_: u8 = 0;
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_unused_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v_a_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_a_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2954_: u8 = 0;
    let mut v_a_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_a_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_a_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2846_);
                v___x_2858_ = l_Lean_Meta_getDecLevel(
                    v_type_2846_,
                    v_a_2853_,
                    v_a_2854_,
                    v_a_2855_,
                    v_a_2856_,
                );
                if crate::leanh::lean_obj_tag(v___x_2858_) == 0 {
                    v_a_2859_ = crate::leanh::lean_ctor_get(v___x_2858_, 0);
                    crate::leanh::lean_inc_n(v_a_2859_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2858_, 1);
                    v___x_2860_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0;
                    v___x_2861_ = crate::leanh::lean_box(0);
                    v___x_2862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v_a_2859_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                    crate::leanh::lean_inc_ref(v___x_2862_);
                    v___x_2863_ = l_Lean_mkConst(v___x_2860_, v___x_2862_);
                    crate::leanh::lean_inc_ref(v_type_2846_);
                    v___x_2864_ = l_Lean_Expr_app___override(v___x_2863_, v_type_2846_);
                    v___x_2865_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2864_,
                        v_a_2853_,
                        v_a_2854_,
                        v_a_2855_,
                        v_a_2856_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2865_) == 0 {
                        v_a_2866_ = crate::leanh::lean_ctor_get(v___x_2865_, 0);
                        v_isSharedCheck_2968_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2865_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2868_ = v___x_2865_;
                            v_isShared_2869_ = v_isSharedCheck_2968_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2866_);
                            crate::leanh::lean_dec(v___x_2865_);
                            v___x_2868_ = crate::leanh::lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2968_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2862_, 2);
                        crate::leanh::lean_dec(v_a_2859_);
                        crate::leanh::lean_dec_ref(v_type_2846_);
                        v_a_2969_ = crate::leanh::lean_ctor_get(v___x_2865_, 0);
                        v_isSharedCheck_2976_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2865_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2971_ = v___x_2865_;
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2969_);
                            crate::leanh::lean_dec(v___x_2865_);
                            v___x_2971_ = crate::leanh::lean_box(0);
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2846_);
                    v_a_2977_ = crate::leanh::lean_ctor_get(v___x_2858_, 0);
                    v_isSharedCheck_2984_ = (!crate::leanh::lean_is_exclusive(v___x_2858_)) as u8;
                    if v_isSharedCheck_2984_ == 0 {
                        v___x_2979_ = v___x_2858_;
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2977_);
                        crate::leanh::lean_dec(v___x_2858_);
                        v___x_2979_ = crate::leanh::lean_box(0);
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2866_) == 1 {
                    crate::leanh::lean_del_object(v___x_2868_);
                    v_options_2870_ = crate::leanh::lean_ctor_get(v_a_2855_, 2);
                    v_val_2871_ = crate::leanh::lean_ctor_get(v_a_2866_, 0);
                    v_isSharedCheck_2963_ = (!crate::leanh::lean_is_exclusive(v_a_2866_)) as u8;
                    if v_isSharedCheck_2963_ == 0 {
                        v___x_2873_ = v_a_2866_;
                        v_isShared_2874_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2871_);
                        crate::leanh::lean_dec(v_a_2866_);
                        v___x_2873_ = crate::leanh::lean_box(0);
                        v_isShared_2874_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2866_);
                    crate::leanh::lean_dec_ref_known(v___x_2862_, 2);
                    crate::leanh::lean_dec(v_a_2859_);
                    crate::leanh::lean_dec_ref(v_type_2846_);
                    v___x_2964_ = crate::leanh::lean_box(0);
                    if v_isShared_2869_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2964_);
                        v___x_2966_ = v___x_2868_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                        v___x_2966_ = v_reuseFailAlloc_2967_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2875_ = crate::leanh::lean_ctor_get(v_a_2855_, 13);
                v_hasTrace_2876_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_2870_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2877_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11;
                v___x_2878_ = l_Lean_mkConst(v___x_2877_, v___x_2862_);
                crate::leanh::lean_inc(v_val_2871_);
                crate::leanh::lean_inc_ref(v_type_2846_);
                v___x_2879_ = l_Lean_mkAppB(v___x_2878_, v_type_2846_, v_val_2871_);
                if v_hasTrace_2876_ == 0 {
                    v___y_2881_ = v_a_2847_;
                    v___y_2882_ = v_a_2848_;
                    v___y_2883_ = v_a_2849_;
                    v___y_2884_ = v_a_2850_;
                    v___y_2885_ = v_a_2851_;
                    v___y_2886_ = v_a_2852_;
                    v___y_2887_ = v_a_2853_;
                    v___y_2888_ = v_a_2854_;
                    v___y_2889_ = v_a_2855_;
                    v___y_2890_ = v_a_2856_;
                    state = 3;
                    continue;
                } else {
                    v___x_2939_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6;
                    v___x_2940_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
                    v___x_2941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2875_,
                        v_options_2870_,
                        v___x_2940_,
                    );
                    if v___x_2941_ == 0 {
                        v___y_2881_ = v_a_2847_;
                        v___y_2882_ = v_a_2848_;
                        v___y_2883_ = v_a_2849_;
                        v___y_2884_ = v_a_2850_;
                        v___y_2885_ = v_a_2851_;
                        v___y_2886_ = v_a_2852_;
                        v___y_2887_ = v_a_2853_;
                        v___y_2888_ = v_a_2854_;
                        v___y_2889_ = v_a_2855_;
                        v___y_2890_ = v_a_2856_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2942_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_,
                            v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2942_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2942_, 1);
                            v___x_2943_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
                            crate::leanh::lean_inc_ref(v_type_2846_);
                            v___x_2944_ = l_Lean_MessageData_ofExpr(v_type_2846_);
                            v___x_2945_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2943_);
                            crate::leanh::lean_ctor_set(v___x_2945_, 1, v___x_2944_);
                            v___x_2946_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2939_, v___x_2945_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
                            if crate::leanh::lean_obj_tag(v___x_2946_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2946_, 1);
                                v___y_2881_ = v_a_2847_;
                                v___y_2882_ = v_a_2848_;
                                v___y_2883_ = v_a_2849_;
                                v___y_2884_ = v_a_2850_;
                                v___y_2885_ = v_a_2851_;
                                v___y_2886_ = v_a_2852_;
                                v___y_2887_ = v_a_2853_;
                                v___y_2888_ = v_a_2854_;
                                v___y_2889_ = v_a_2855_;
                                v___y_2890_ = v_a_2856_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2879_);
                                crate::leanh::lean_del_object(v___x_2873_);
                                crate::leanh::lean_dec(v_val_2871_);
                                crate::leanh::lean_dec(v_a_2859_);
                                crate::leanh::lean_dec_ref(v_type_2846_);
                                v_a_2947_ = crate::leanh::lean_ctor_get(v___x_2946_, 0);
                                v_isSharedCheck_2954_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2946_)) as u8;
                                if v_isSharedCheck_2954_ == 0 {
                                    v___x_2949_ = v___x_2946_;
                                    v_isShared_2950_ = v_isSharedCheck_2954_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2947_);
                                    crate::leanh::lean_dec(v___x_2946_);
                                    v___x_2949_ = crate::leanh::lean_box(0);
                                    v_isShared_2950_ = v_isSharedCheck_2954_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2879_);
                            crate::leanh::lean_del_object(v___x_2873_);
                            crate::leanh::lean_dec(v_val_2871_);
                            crate::leanh::lean_dec(v_a_2859_);
                            crate::leanh::lean_dec_ref(v_type_2846_);
                            v_a_2955_ = crate::leanh::lean_ctor_get(v___x_2942_, 0);
                            v_isSharedCheck_2962_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2942_)) as u8;
                            if v_isSharedCheck_2962_ == 0 {
                                v___x_2957_ = v___x_2942_;
                                v_isShared_2958_ = v_isSharedCheck_2962_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2955_);
                                crate::leanh::lean_dec(v___x_2942_);
                                v___x_2957_ = crate::leanh::lean_box(0);
                                v_isShared_2958_ = v_isSharedCheck_2962_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2879_);
                crate::leanh::lean_inc_ref(v_type_2846_);
                crate::leanh::lean_inc(v_a_2859_);
                v___x_2891_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
                    v_a_2859_,
                    v_type_2846_,
                    v___x_2879_,
                    v___y_2881_,
                    v___y_2882_,
                    v___y_2883_,
                    v___y_2884_,
                    v___y_2885_,
                    v___y_2886_,
                    v___y_2887_,
                    v___y_2888_,
                    v___y_2889_,
                    v___y_2890_,
                );
                if crate::leanh::lean_obj_tag(v___x_2891_) == 0 {
                    v_a_2892_ = crate::leanh::lean_ctor_get(v___x_2891_, 0);
                    crate::leanh::lean_inc(v_a_2892_);
                    crate::leanh::lean_dec_ref_known(v___x_2891_, 1);
                    v___x_2893_ =
                        l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_2881_, v___y_2889_);
                    if crate::leanh::lean_obj_tag(v___x_2893_) == 0 {
                        v_a_2894_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                        crate::leanh::lean_inc(v_a_2894_);
                        crate::leanh::lean_dec_ref_known(v___x_2893_, 1);
                        v_ncRings_2895_ = crate::leanh::lean_ctor_get(v_a_2894_, 6);
                        crate::leanh::lean_inc_ref(v_ncRings_2895_);
                        crate::leanh::lean_dec(v_a_2894_);
                        v___x_2896_ = lean_array_get_size(v_ncRings_2895_);
                        crate::leanh::lean_dec_ref(v_ncRings_2895_);
                        v___x_2897_ = crate::leanh::lean_box(0);
                        v___x_2898_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                        v___x_2899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
                        v___x_2900_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2900_, 0, v___x_2896_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 1, v_type_2846_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 2, v_a_2859_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 3, v_val_2871_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 4, v___x_2879_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 5, v_a_2892_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 6, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 7, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 8, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 9, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 10, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 11, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 12, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 13, v___x_2897_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 14, v___x_2898_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 15, v___x_2899_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 16, v___x_2899_);
                        v___f_2901_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_2901_, 0, v___x_2900_);
                        v___x_2902_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_2903_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2902_, v___f_2901_, v___y_2881_);
                        if crate::leanh::lean_obj_tag(v___x_2903_) == 0 {
                            v_isSharedCheck_2913_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2913_ == 0 {
                                v_unused_2914_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                                crate::leanh::lean_dec(v_unused_2914_);
                                v___x_2905_ = v___x_2903_;
                                v_isShared_2906_ = v_isSharedCheck_2913_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2903_);
                                v___x_2905_ = crate::leanh::lean_box(0);
                                v_isShared_2906_ = v_isSharedCheck_2913_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2873_);
                            v_a_2915_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                            v_isSharedCheck_2922_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2922_ == 0 {
                                v___x_2917_ = v___x_2903_;
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2915_);
                                crate::leanh::lean_dec(v___x_2903_);
                                v___x_2917_ = crate::leanh::lean_box(0);
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2892_);
                        crate::leanh::lean_dec_ref(v___x_2879_);
                        crate::leanh::lean_del_object(v___x_2873_);
                        crate::leanh::lean_dec(v_val_2871_);
                        crate::leanh::lean_dec(v_a_2859_);
                        crate::leanh::lean_dec_ref(v_type_2846_);
                        v_a_2923_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2930_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2930_ == 0 {
                            v___x_2925_ = v___x_2893_;
                            v_isShared_2926_ = v_isSharedCheck_2930_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2923_);
                            crate::leanh::lean_dec(v___x_2893_);
                            v___x_2925_ = crate::leanh::lean_box(0);
                            v_isShared_2926_ = v_isSharedCheck_2930_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2879_);
                    crate::leanh::lean_del_object(v___x_2873_);
                    crate::leanh::lean_dec(v_val_2871_);
                    crate::leanh::lean_dec(v_a_2859_);
                    crate::leanh::lean_dec_ref(v_type_2846_);
                    v_a_2931_ = crate::leanh::lean_ctor_get(v___x_2891_, 0);
                    v_isSharedCheck_2938_ = (!crate::leanh::lean_is_exclusive(v___x_2891_)) as u8;
                    if v_isSharedCheck_2938_ == 0 {
                        v___x_2933_ = v___x_2891_;
                        v_isShared_2934_ = v_isSharedCheck_2938_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2931_);
                        crate::leanh::lean_dec(v___x_2891_);
                        v___x_2933_ = crate::leanh::lean_box(0);
                        v_isShared_2934_ = v_isSharedCheck_2938_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2873_, 0, v___x_2896_);
                    v___x_2908_ = v___x_2873_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2896_);
                    v___x_2908_ = v_reuseFailAlloc_2912_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2905_, 0, v___x_2908_);
                    v___x_2910_ = v___x_2905_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2910_;
            }
            7 => {
                if v_isShared_2918_ == 0 {
                    v___x_2920_ = v___x_2917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
                    v___x_2920_ = v_reuseFailAlloc_2921_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2920_;
            }
            9 => {
                if v_isShared_2926_ == 0 {
                    v___x_2928_ = v___x_2925_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
                    v___x_2928_ = v_reuseFailAlloc_2929_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2928_;
            }
            11 => {
                if v_isShared_2934_ == 0 {
                    v___x_2936_ = v___x_2933_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2937_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
                    v___x_2936_ = v_reuseFailAlloc_2937_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2936_;
            }
            13 => {
                if v_isShared_2950_ == 0 {
                    v___x_2952_ = v___x_2949_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2952_;
            }
            15 => {
                if v_isShared_2958_ == 0 {
                    v___x_2960_ = v___x_2957_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
                    v___x_2960_ = v_reuseFailAlloc_2961_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2960_;
            }
            17 => {
                return v___x_2966_;
            }
            18 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2974_;
            }
            20 => {
                if v_isShared_2980_ == 0 {
                    v___x_2982_ = v___x_2979_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(
    mut v_type_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
    mut v_a_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
    crate::leanh::lean_dec(v_a_2995_);
    crate::leanh::lean_dec_ref(v_a_2994_);
    crate::leanh::lean_dec(v_a_2993_);
    crate::leanh::lean_dec_ref(v_a_2992_);
    crate::leanh::lean_dec(v_a_2991_);
    crate::leanh::lean_dec_ref(v_a_2990_);
    crate::leanh::lean_dec(v_a_2989_);
    crate::leanh::lean_dec_ref(v_a_2988_);
    crate::leanh::lean_dec(v_a_2987_);
    crate::leanh::lean_dec(v_a_2986_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(
    mut v_type_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_s_3000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3014_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3001_ = crate::leanh::lean_ctor_get(v_s_3000_, 0);
                v_typeIdOf_3002_ = crate::leanh::lean_ctor_get(v_s_3000_, 1);
                v_exprToRingId_3003_ = crate::leanh::lean_ctor_get(v_s_3000_, 2);
                v_semirings_3004_ = crate::leanh::lean_ctor_get(v_s_3000_, 3);
                v_stypeIdOf_3005_ = crate::leanh::lean_ctor_get(v_s_3000_, 4);
                v_exprToSemiringId_3006_ = crate::leanh::lean_ctor_get(v_s_3000_, 5);
                v_ncRings_3007_ = crate::leanh::lean_ctor_get(v_s_3000_, 6);
                v_exprToNCRingId_3008_ = crate::leanh::lean_ctor_get(v_s_3000_, 7);
                v_nctypeIdOf_3009_ = crate::leanh::lean_ctor_get(v_s_3000_, 8);
                v_ncSemirings_3010_ = crate::leanh::lean_ctor_get(v_s_3000_, 9);
                v_exprToNCSemiringId_3011_ = crate::leanh::lean_ctor_get(v_s_3000_, 10);
                v_ncstypeIdOf_3012_ = crate::leanh::lean_ctor_get(v_s_3000_, 11);
                v_steps_3013_ = crate::leanh::lean_ctor_get(v_s_3000_, 12);
                v_reportedMaxDegreeIssue_3014_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3000_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3022_ = (!crate::leanh::lean_is_exclusive(v_s_3000_)) as u8;
                if v_isSharedCheck_3022_ == 0 {
                    v___x_3016_ = v_s_3000_;
                    v_isShared_3017_ = v_isSharedCheck_3022_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_3013_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_3012_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_3011_);
                    crate::leanh::lean_inc(v_ncSemirings_3010_);
                    crate::leanh::lean_inc(v_nctypeIdOf_3009_);
                    crate::leanh::lean_inc(v_exprToNCRingId_3008_);
                    crate::leanh::lean_inc(v_ncRings_3007_);
                    crate::leanh::lean_inc(v_exprToSemiringId_3006_);
                    crate::leanh::lean_inc(v_stypeIdOf_3005_);
                    crate::leanh::lean_inc(v_semirings_3004_);
                    crate::leanh::lean_inc(v_exprToRingId_3003_);
                    crate::leanh::lean_inc(v_typeIdOf_3002_);
                    crate::leanh::lean_inc(v_rings_3001_);
                    crate::leanh::lean_dec(v_s_3000_);
                    v___x_3016_ = crate::leanh::lean_box(0);
                    v_isShared_3017_ = v_isSharedCheck_3022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3018_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_3009_, v_type_2998_, v_a_2999_);
                if v_isShared_3017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3016_, 8, v___x_3018_);
                    v___x_3020_ = v___x_3016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_rings_3001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_typeIdOf_3002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_exprToRingId_3003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_semirings_3004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_stypeIdOf_3005_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3021_,
                        5,
                        v_exprToSemiringId_3006_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 6, v_ncRings_3007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 7, v_exprToNCRingId_3008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 8, v___x_3018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 9, v_ncSemirings_3010_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3021_,
                        10,
                        v_exprToNCSemiringId_3011_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 11, v_ncstypeIdOf_3012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 12, v_steps_3013_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3021_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3014_,
                    );
                    v___x_3020_ = v_reuseFailAlloc_3021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(
    mut v_type_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v_nctypeIdOf_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_unused_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_a_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3035_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3024_, v_a_3032_);
                if crate::leanh::lean_obj_tag(v___x_3035_) == 0 {
                    v_a_3036_ = crate::leanh::lean_ctor_get(v___x_3035_, 0);
                    v_isSharedCheck_3067_ = (!crate::leanh::lean_is_exclusive(v___x_3035_)) as u8;
                    if v_isSharedCheck_3067_ == 0 {
                        v___x_3038_ = v___x_3035_;
                        v_isShared_3039_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3036_);
                        crate::leanh::lean_dec(v___x_3035_);
                        v___x_3038_ = crate::leanh::lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3023_);
                    v_a_3068_ = crate::leanh::lean_ctor_get(v___x_3035_, 0);
                    v_isSharedCheck_3075_ = (!crate::leanh::lean_is_exclusive(v___x_3035_)) as u8;
                    if v_isSharedCheck_3075_ == 0 {
                        v___x_3070_ = v___x_3035_;
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3068_);
                        crate::leanh::lean_dec(v___x_3035_);
                        v___x_3070_ = crate::leanh::lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_nctypeIdOf_3040_ = crate::leanh::lean_ctor_get(v_a_3036_, 8);
                crate::leanh::lean_inc_ref(v_nctypeIdOf_3040_);
                crate::leanh::lean_dec(v_a_3036_);
                v___x_3041_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_3040_, v_type_3023_);
                crate::leanh::lean_dec_ref(v_nctypeIdOf_3040_);
                if crate::leanh::lean_obj_tag(v___x_3041_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_3023_);
                    v_val_3042_ = crate::leanh::lean_ctor_get(v___x_3041_, 0);
                    crate::leanh::lean_inc(v_val_3042_);
                    crate::leanh::lean_dec_ref_known(v___x_3041_, 1);
                    if v_isShared_3039_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3038_, 0, v_val_3042_);
                        v___x_3044_ = v___x_3038_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_val_3042_);
                        v___x_3044_ = v_reuseFailAlloc_3045_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3041_);
                    crate::leanh::lean_del_object(v___x_3038_);
                    crate::leanh::lean_inc_ref(v_type_3023_);
                    v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
                    if crate::leanh::lean_obj_tag(v___x_3046_) == 0 {
                        v_a_3047_ = crate::leanh::lean_ctor_get(v___x_3046_, 0);
                        crate::leanh::lean_inc_n(v_a_3047_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3046_, 1);
                        v___f_3048_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3048_, 0, v_type_3023_);
                        crate::leanh::lean_closure_set(v___f_3048_, 1, v_a_3047_);
                        v___x_3049_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3050_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3049_, v___f_3048_, v_a_3024_);
                        if crate::leanh::lean_obj_tag(v___x_3050_) == 0 {
                            v_isSharedCheck_3057_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3050_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v_unused_3058_ = crate::leanh::lean_ctor_get(v___x_3050_, 0);
                                crate::leanh::lean_dec(v_unused_3058_);
                                v___x_3052_ = v___x_3050_;
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3050_);
                                v___x_3052_ = crate::leanh::lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3047_);
                            v_a_3059_ = crate::leanh::lean_ctor_get(v___x_3050_, 0);
                            v_isSharedCheck_3066_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3050_)) as u8;
                            if v_isSharedCheck_3066_ == 0 {
                                v___x_3061_ = v___x_3050_;
                                v_isShared_3062_ = v_isSharedCheck_3066_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3059_);
                                crate::leanh::lean_dec(v___x_3050_);
                                v___x_3061_ = crate::leanh::lean_box(0);
                                v_isShared_3062_ = v_isSharedCheck_3066_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_3023_);
                        return v___x_3046_;
                    }
                }
            }
            2 => {
                return v___x_3044_;
            }
            3 => {
                if v_isShared_3053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3052_, 0, v_a_3047_);
                    v___x_3055_ = v___x_3052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3047_);
                    v___x_3055_ = v_reuseFailAlloc_3056_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3055_;
            }
            5 => {
                if v_isShared_3062_ == 0 {
                    v___x_3064_ = v___x_3061_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
                    v___x_3064_ = v_reuseFailAlloc_3065_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3064_;
            }
            7 => {
                if v_isShared_3071_ == 0 {
                    v___x_3073_ = v___x_3070_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
                    v___x_3073_ = v_reuseFailAlloc_3074_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(
    mut v_type_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
    mut v_a_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3088_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(
        v_type_3076_,
        v_a_3077_,
        v_a_3078_,
        v_a_3079_,
        v_a_3080_,
        v_a_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    crate::leanh::lean_dec(v_a_3086_);
    crate::leanh::lean_dec_ref(v_a_3085_);
    crate::leanh::lean_dec(v_a_3084_);
    crate::leanh::lean_dec_ref(v_a_3083_);
    crate::leanh::lean_dec(v_a_3082_);
    crate::leanh::lean_dec_ref(v_a_3081_);
    crate::leanh::lean_dec(v_a_3080_);
    crate::leanh::lean_dec_ref(v_a_3079_);
    crate::leanh::lean_dec(v_a_3078_);
    crate::leanh::lean_dec(v_a_3077_);
    return v_res_3088_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(
    mut v_semiringId_3089_: *mut crate::leanh::LeanObject,
    mut v_s_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_3104_: u8 = 0;
    let mut v_invSet_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_3108_: u8 = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_unused_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_3091_ = crate::leanh::lean_ctor_get(v_s_3090_, 0);
                v_invFn_x3f_3092_ = crate::leanh::lean_ctor_get(v_s_3090_, 1);
                v_commSemiringInst_3093_ = crate::leanh::lean_ctor_get(v_s_3090_, 3);
                v_commRingInst_3094_ = crate::leanh::lean_ctor_get(v_s_3090_, 4);
                v_noZeroDivInst_x3f_3095_ = crate::leanh::lean_ctor_get(v_s_3090_, 5);
                v_fieldInst_x3f_3096_ = crate::leanh::lean_ctor_get(v_s_3090_, 6);
                v_powIdentityInst_x3f_3097_ = crate::leanh::lean_ctor_get(v_s_3090_, 7);
                v_denoteEntries_3098_ = crate::leanh::lean_ctor_get(v_s_3090_, 8);
                v_nextId_3099_ = crate::leanh::lean_ctor_get(v_s_3090_, 9);
                v_steps_3100_ = crate::leanh::lean_ctor_get(v_s_3090_, 10);
                v_queue_3101_ = crate::leanh::lean_ctor_get(v_s_3090_, 11);
                v_basis_3102_ = crate::leanh::lean_ctor_get(v_s_3090_, 12);
                v_diseqs_3103_ = crate::leanh::lean_ctor_get(v_s_3090_, 13);
                v_recheck_3104_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_3105_ = crate::leanh::lean_ctor_get(v_s_3090_, 14);
                v_powIdentityVarCount_3106_ = crate::leanh::lean_ctor_get(v_s_3090_, 15);
                v_numEq0_x3f_3107_ = crate::leanh::lean_ctor_get(v_s_3090_, 16);
                v_numEq0Updated_3108_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_3116_ = (!crate::leanh::lean_is_exclusive(v_s_3090_)) as u8;
                if v_isSharedCheck_3116_ == 0 {
                    v_unused_3117_ = crate::leanh::lean_ctor_get(v_s_3090_, 2);
                    crate::leanh::lean_dec(v_unused_3117_);
                    v___x_3110_ = v_s_3090_;
                    v_isShared_3111_ = v_isSharedCheck_3116_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_3107_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_3106_);
                    crate::leanh::lean_inc(v_invSet_3105_);
                    crate::leanh::lean_inc(v_diseqs_3103_);
                    crate::leanh::lean_inc(v_basis_3102_);
                    crate::leanh::lean_inc(v_queue_3101_);
                    crate::leanh::lean_inc(v_steps_3100_);
                    crate::leanh::lean_inc(v_nextId_3099_);
                    crate::leanh::lean_inc(v_denoteEntries_3098_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_3097_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_3096_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_3095_);
                    crate::leanh::lean_inc(v_commRingInst_3094_);
                    crate::leanh::lean_inc(v_commSemiringInst_3093_);
                    crate::leanh::lean_inc(v_invFn_x3f_3092_);
                    crate::leanh::lean_inc(v_toRing_3091_);
                    crate::leanh::lean_dec(v_s_3090_);
                    v___x_3110_ = crate::leanh::lean_box(0);
                    v_isShared_3111_ = v_isSharedCheck_3116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3112_, 0, v_semiringId_3089_);
                if v_isShared_3111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3110_, 2, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_toRing_3091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_invFn_x3f_3092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 2, v___x_3112_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3115_,
                        3,
                        v_commSemiringInst_3093_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_commRingInst_3094_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3115_,
                        5,
                        v_noZeroDivInst_x3f_3095_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 6, v_fieldInst_x3f_3096_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3115_,
                        7,
                        v_powIdentityInst_x3f_3097_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 8, v_denoteEntries_3098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 9, v_nextId_3099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 10, v_steps_3100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 11, v_queue_3101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 12, v_basis_3102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 13, v_diseqs_3103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 14, v_invSet_3105_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3115_,
                        15,
                        v_powIdentityVarCount_3106_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 16, v_numEq0_x3f_3107_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3115_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_3104_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3115_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_3108_,
                    );
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(
    mut v_ringId_3118_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3119_: *mut crate::leanh::LeanObject,
    mut v_a_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3122_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_3122_, 0, v_semiringId_3119_);
    v___x_3123_ = 0;
    v___x_3124_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3124_, 0, v_ringId_3118_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3124_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3123_,
    );
    v___x_3125_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v___f_3122_,
        v___x_3124_,
        v_a_3120_,
    );
    crate::leanh::lean_dec_ref_known(v___x_3124_, 1);
    return v___x_3125_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(
    mut v_ringId_3126_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3130_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_3126_, v_semiringId_3127_, v_a_3128_);
    crate::leanh::lean_dec(v_a_3128_);
    return v_res_3130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(
    mut v_ringId_3131_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_a_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3144_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_3131_, v_semiringId_3132_, v_a_3133_);
    return v___x_3144_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(
    mut v_ringId_3145_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
    mut v_a_3148_: *mut crate::leanh::LeanObject,
    mut v_a_3149_: *mut crate::leanh::LeanObject,
    mut v_a_3150_: *mut crate::leanh::LeanObject,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
    mut v_a_3155_: *mut crate::leanh::LeanObject,
    mut v_a_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_3145_, v_semiringId_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
    crate::leanh::lean_dec(v_a_3156_);
    crate::leanh::lean_dec_ref(v_a_3155_);
    crate::leanh::lean_dec(v_a_3154_);
    crate::leanh::lean_dec_ref(v_a_3153_);
    crate::leanh::lean_dec(v_a_3152_);
    crate::leanh::lean_dec_ref(v_a_3151_);
    crate::leanh::lean_dec(v_a_3150_);
    crate::leanh::lean_dec_ref(v_a_3149_);
    crate::leanh::lean_dec(v_a_3148_);
    crate::leanh::lean_dec(v_a_3147_);
    return v_res_3158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(
    mut v___x_3159_: *mut crate::leanh::LeanObject,
    mut v_s_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3174_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3161_ = crate::leanh::lean_ctor_get(v_s_3160_, 0);
                v_typeIdOf_3162_ = crate::leanh::lean_ctor_get(v_s_3160_, 1);
                v_exprToRingId_3163_ = crate::leanh::lean_ctor_get(v_s_3160_, 2);
                v_semirings_3164_ = crate::leanh::lean_ctor_get(v_s_3160_, 3);
                v_stypeIdOf_3165_ = crate::leanh::lean_ctor_get(v_s_3160_, 4);
                v_exprToSemiringId_3166_ = crate::leanh::lean_ctor_get(v_s_3160_, 5);
                v_ncRings_3167_ = crate::leanh::lean_ctor_get(v_s_3160_, 6);
                v_exprToNCRingId_3168_ = crate::leanh::lean_ctor_get(v_s_3160_, 7);
                v_nctypeIdOf_3169_ = crate::leanh::lean_ctor_get(v_s_3160_, 8);
                v_ncSemirings_3170_ = crate::leanh::lean_ctor_get(v_s_3160_, 9);
                v_exprToNCSemiringId_3171_ = crate::leanh::lean_ctor_get(v_s_3160_, 10);
                v_ncstypeIdOf_3172_ = crate::leanh::lean_ctor_get(v_s_3160_, 11);
                v_steps_3173_ = crate::leanh::lean_ctor_get(v_s_3160_, 12);
                v_reportedMaxDegreeIssue_3174_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3160_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3182_ = (!crate::leanh::lean_is_exclusive(v_s_3160_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3176_ = v_s_3160_;
                    v_isShared_3177_ = v_isSharedCheck_3182_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_3173_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_3172_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_3171_);
                    crate::leanh::lean_inc(v_ncSemirings_3170_);
                    crate::leanh::lean_inc(v_nctypeIdOf_3169_);
                    crate::leanh::lean_inc(v_exprToNCRingId_3168_);
                    crate::leanh::lean_inc(v_ncRings_3167_);
                    crate::leanh::lean_inc(v_exprToSemiringId_3166_);
                    crate::leanh::lean_inc(v_stypeIdOf_3165_);
                    crate::leanh::lean_inc(v_semirings_3164_);
                    crate::leanh::lean_inc(v_exprToRingId_3163_);
                    crate::leanh::lean_inc(v_typeIdOf_3162_);
                    crate::leanh::lean_inc(v_rings_3161_);
                    crate::leanh::lean_dec(v_s_3160_);
                    v___x_3176_ = crate::leanh::lean_box(0);
                    v_isShared_3177_ = v_isSharedCheck_3182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3178_ = lean_array_push(v_semirings_3164_, v___x_3159_);
                if v_isShared_3177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3176_, 3, v___x_3178_);
                    v___x_3180_ = v___x_3176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_rings_3161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_typeIdOf_3162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_exprToRingId_3163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 3, v___x_3178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_stypeIdOf_3165_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3181_,
                        5,
                        v_exprToSemiringId_3166_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_ncRings_3167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_exprToNCRingId_3168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 8, v_nctypeIdOf_3169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 9, v_ncSemirings_3170_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3181_,
                        10,
                        v_exprToNCSemiringId_3171_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 11, v_ncstypeIdOf_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 12, v_steps_3173_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3181_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3174_,
                    );
                    v___x_3180_ = v_reuseFailAlloc_3181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(
    mut v_msg_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3189_ = crate::leanh::lean_ctor_get(v___y_3186_, 5);
                v___x_3190_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
                v_a_3191_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                v_isSharedCheck_3199_ = (!crate::leanh::lean_is_exclusive(v___x_3190_)) as u8;
                if v_isSharedCheck_3199_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    v_isShared_3194_ = v_isSharedCheck_3199_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3191_);
                    crate::leanh::lean_dec(v___x_3190_);
                    v___x_3193_ = crate::leanh::lean_box(0);
                    v_isShared_3194_ = v_isSharedCheck_3199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3189_);
                v___x_3195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3195_, 0, v_ref_3189_);
                crate::leanh::lean_ctor_set(v___x_3195_, 1, v_a_3191_);
                if v_isShared_3194_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3193_, 1);
                    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3195_);
                    v___x_3197_ = v___x_3193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(
    mut v_msg_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3206_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
    crate::leanh::lean_dec(v___y_3204_);
    crate::leanh::lean_dec_ref(v___y_3203_);
    crate::leanh::lean_dec(v___y_3202_);
    crate::leanh::lean_dec_ref(v___y_3201_);
    return v_res_3206_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3225_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3225_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3226_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6);
    v___x_3227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3229_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8;
    v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
    return v___x_3230_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(
    mut v_type_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
    mut v_a_3240_: *mut crate::leanh::LeanObject,
    mut v_a_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v_val_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut v_unused_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_a_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3311_: u8 = 0;
    let mut v_a_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3328_: u8 = 0;
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v_a_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v_a_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_a_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_3231_);
                v___x_3243_ = l_Lean_Meta_getDecLevel(
                    v_type_3231_,
                    v_a_3238_,
                    v_a_3239_,
                    v_a_3240_,
                    v_a_3241_,
                );
                if crate::leanh::lean_obj_tag(v___x_3243_) == 0 {
                    v_a_3244_ = crate::leanh::lean_ctor_get(v___x_3243_, 0);
                    crate::leanh::lean_inc_n(v_a_3244_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3243_, 1);
                    v___x_3245_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1;
                    v___x_3246_ = crate::leanh::lean_box(0);
                    v___x_3247_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3247_, 0, v_a_3244_);
                    crate::leanh::lean_ctor_set(v___x_3247_, 1, v___x_3246_);
                    crate::leanh::lean_inc_ref(v___x_3247_);
                    v___x_3248_ = l_Lean_mkConst(v___x_3245_, v___x_3247_);
                    crate::leanh::lean_inc_ref(v_type_3231_);
                    v___x_3249_ = l_Lean_Expr_app___override(v___x_3248_, v_type_3231_);
                    v___x_3250_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3249_,
                        v_a_3238_,
                        v_a_3239_,
                        v_a_3240_,
                        v_a_3241_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3250_) == 0 {
                        v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                        v_isSharedCheck_3345_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3345_ == 0 {
                            v___x_3253_ = v___x_3250_;
                            v_isShared_3254_ = v_isSharedCheck_3345_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3251_);
                            crate::leanh::lean_dec(v___x_3250_);
                            v___x_3253_ = crate::leanh::lean_box(0);
                            v_isShared_3254_ = v_isSharedCheck_3345_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3247_, 2);
                        crate::leanh::lean_dec(v_a_3244_);
                        crate::leanh::lean_dec_ref(v_type_3231_);
                        v_a_3346_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                        v_isSharedCheck_3353_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3353_ == 0 {
                            v___x_3348_ = v___x_3250_;
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3346_);
                            crate::leanh::lean_dec(v___x_3250_);
                            v___x_3348_ = crate::leanh::lean_box(0);
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3231_);
                    v_a_3354_ = crate::leanh::lean_ctor_get(v___x_3243_, 0);
                    v_isSharedCheck_3361_ = (!crate::leanh::lean_is_exclusive(v___x_3243_)) as u8;
                    if v_isSharedCheck_3361_ == 0 {
                        v___x_3356_ = v___x_3243_;
                        v_isShared_3357_ = v_isSharedCheck_3361_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3354_);
                        crate::leanh::lean_dec(v___x_3243_);
                        v___x_3356_ = crate::leanh::lean_box(0);
                        v_isShared_3357_ = v_isSharedCheck_3361_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3251_) == 1 {
                    crate::leanh::lean_del_object(v___x_3253_);
                    v_val_3255_ = crate::leanh::lean_ctor_get(v_a_3251_, 0);
                    crate::leanh::lean_inc_n(v_val_3255_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_3251_, 1);
                    v___x_3256_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2;
                    crate::leanh::lean_inc_ref(v___x_3247_);
                    v___x_3257_ = l_Lean_mkConst(v___x_3256_, v___x_3247_);
                    crate::leanh::lean_inc_ref_n(v_type_3231_, 2);
                    v___x_3258_ = l_Lean_mkAppB(v___x_3257_, v_type_3231_, v_val_3255_);
                    v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5;
                    v___x_3260_ = l_Lean_mkConst(v___x_3259_, v___x_3247_);
                    crate::leanh::lean_inc_ref(v___x_3258_);
                    v___x_3261_ = l_Lean_mkAppB(v___x_3260_, v_type_3231_, v___x_3258_);
                    v___x_3262_ = l_Lean_Meta_Sym_canon(
                        v___x_3261_,
                        v_a_3236_,
                        v_a_3237_,
                        v_a_3238_,
                        v_a_3239_,
                        v_a_3240_,
                        v_a_3241_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        crate::leanh::lean_inc(v_a_3263_);
                        crate::leanh::lean_dec_ref_known(v___x_3262_, 1);
                        v___x_3264_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3263_, v_a_3237_);
                        if crate::leanh::lean_obj_tag(v___x_3264_) == 0 {
                            v_a_3265_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                            crate::leanh::lean_inc_n(v_a_3265_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_3264_, 1);
                            v___x_3266_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                                v_a_3265_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_,
                                v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3266_) == 0 {
                                v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                                crate::leanh::lean_inc(v_a_3267_);
                                crate::leanh::lean_dec_ref_known(v___x_3266_, 1);
                                if crate::leanh::lean_obj_tag(v_a_3267_) == 1 {
                                    crate::leanh::lean_dec(v_a_3265_);
                                    v_val_3268_ = crate::leanh::lean_ctor_get(v_a_3267_, 0);
                                    v_isSharedCheck_3320_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_3267_)) as u8;
                                    if v_isSharedCheck_3320_ == 0 {
                                        v___x_3270_ = v_a_3267_;
                                        v_isShared_3271_ = v_isSharedCheck_3320_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_3268_);
                                        crate::leanh::lean_dec(v_a_3267_);
                                        v___x_3270_ = crate::leanh::lean_box(0);
                                        v_isShared_3271_ = v_isSharedCheck_3320_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3267_);
                                    crate::leanh::lean_dec_ref(v___x_3258_);
                                    crate::leanh::lean_dec(v_val_3255_);
                                    crate::leanh::lean_dec(v_a_3244_);
                                    crate::leanh::lean_dec_ref(v_type_3231_);
                                    v___x_3321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9);
                                    v___x_3322_ = l_Lean_indentExpr(v_a_3265_);
                                    v___x_3323_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3323_, 0, v___x_3321_);
                                    crate::leanh::lean_ctor_set(v___x_3323_, 1, v___x_3322_);
                                    v___x_3324_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_3323_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
                                    return v___x_3324_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3265_);
                                crate::leanh::lean_dec_ref(v___x_3258_);
                                crate::leanh::lean_dec(v_val_3255_);
                                crate::leanh::lean_dec(v_a_3244_);
                                crate::leanh::lean_dec_ref(v_type_3231_);
                                return v___x_3266_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3258_);
                            crate::leanh::lean_dec(v_val_3255_);
                            crate::leanh::lean_dec(v_a_3244_);
                            crate::leanh::lean_dec_ref(v_type_3231_);
                            v_a_3325_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                            v_isSharedCheck_3332_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3264_)) as u8;
                            if v_isSharedCheck_3332_ == 0 {
                                v___x_3327_ = v___x_3264_;
                                v_isShared_3328_ = v_isSharedCheck_3332_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3325_);
                                crate::leanh::lean_dec(v___x_3264_);
                                v___x_3327_ = crate::leanh::lean_box(0);
                                v_isShared_3328_ = v_isSharedCheck_3332_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3258_);
                        crate::leanh::lean_dec(v_val_3255_);
                        crate::leanh::lean_dec(v_a_3244_);
                        crate::leanh::lean_dec_ref(v_type_3231_);
                        v_a_3333_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3340_ == 0 {
                            v___x_3335_ = v___x_3262_;
                            v_isShared_3336_ = v_isSharedCheck_3340_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3333_);
                            crate::leanh::lean_dec(v___x_3262_);
                            v___x_3335_ = crate::leanh::lean_box(0);
                            v_isShared_3336_ = v_isSharedCheck_3340_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3251_);
                    crate::leanh::lean_dec_ref_known(v___x_3247_, 2);
                    crate::leanh::lean_dec(v_a_3244_);
                    crate::leanh::lean_dec_ref(v_type_3231_);
                    v___x_3341_ = crate::leanh::lean_box(0);
                    if v_isShared_3254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3253_, 0, v___x_3341_);
                        v___x_3343_ = v___x_3253_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
                        v___x_3343_ = v_reuseFailAlloc_3344_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3272_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3232_, v_a_3240_);
                if crate::leanh::lean_obj_tag(v___x_3272_) == 0 {
                    v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3272_, 0);
                    crate::leanh::lean_inc(v_a_3273_);
                    crate::leanh::lean_dec_ref_known(v___x_3272_, 1);
                    v_semirings_3274_ = crate::leanh::lean_ctor_get(v_a_3273_, 3);
                    crate::leanh::lean_inc_ref(v_semirings_3274_);
                    crate::leanh::lean_dec(v_a_3273_);
                    v___x_3275_ = lean_array_get_size(v_semirings_3274_);
                    crate::leanh::lean_dec_ref(v_semirings_3274_);
                    v___x_3276_ = crate::leanh::lean_box(0);
                    v___x_3277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
                    v___x_3278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_3279_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3275_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 1, v_type_3231_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 2, v_a_3244_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 3, v___x_3258_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 4, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 5, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 6, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 7, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 8, v___x_3277_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 9, v___x_3278_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 10, v___x_3277_);
                    crate::leanh::lean_inc(v_val_3268_);
                    v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3280_, 0, v___x_3279_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 1, v_val_3268_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 2, v_val_3255_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 3, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 4, v___x_3276_);
                    v___f_3281_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_3281_, 0, v___x_3280_);
                    v___x_3282_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3283_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3282_, v___f_3281_, v_a_3232_);
                    if crate::leanh::lean_obj_tag(v___x_3283_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3283_, 1);
                        v___x_3284_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_3268_, v___x_3275_, v_a_3232_);
                        if crate::leanh::lean_obj_tag(v___x_3284_) == 0 {
                            v_isSharedCheck_3294_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3284_)) as u8;
                            if v_isSharedCheck_3294_ == 0 {
                                v_unused_3295_ = crate::leanh::lean_ctor_get(v___x_3284_, 0);
                                crate::leanh::lean_dec(v_unused_3295_);
                                v___x_3286_ = v___x_3284_;
                                v_isShared_3287_ = v_isSharedCheck_3294_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3284_);
                                v___x_3286_ = crate::leanh::lean_box(0);
                                v_isShared_3287_ = v_isSharedCheck_3294_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3270_);
                            v_a_3296_ = crate::leanh::lean_ctor_get(v___x_3284_, 0);
                            v_isSharedCheck_3303_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3284_)) as u8;
                            if v_isSharedCheck_3303_ == 0 {
                                v___x_3298_ = v___x_3284_;
                                v_isShared_3299_ = v_isSharedCheck_3303_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3296_);
                                crate::leanh::lean_dec(v___x_3284_);
                                v___x_3298_ = crate::leanh::lean_box(0);
                                v_isShared_3299_ = v_isSharedCheck_3303_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3270_);
                        crate::leanh::lean_dec(v_val_3268_);
                        v_a_3304_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3311_ == 0 {
                            v___x_3306_ = v___x_3283_;
                            v_isShared_3307_ = v_isSharedCheck_3311_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3304_);
                            crate::leanh::lean_dec(v___x_3283_);
                            v___x_3306_ = crate::leanh::lean_box(0);
                            v_isShared_3307_ = v_isSharedCheck_3311_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3270_);
                    crate::leanh::lean_dec(v_val_3268_);
                    crate::leanh::lean_dec_ref(v___x_3258_);
                    crate::leanh::lean_dec(v_val_3255_);
                    crate::leanh::lean_dec(v_a_3244_);
                    crate::leanh::lean_dec_ref(v_type_3231_);
                    v_a_3312_ = crate::leanh::lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3319_ = (!crate::leanh::lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3314_ = v___x_3272_;
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3312_);
                        crate::leanh::lean_dec(v___x_3272_);
                        v___x_3314_ = crate::leanh::lean_box(0);
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3271_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3275_);
                    v___x_3289_ = v___x_3270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3275_);
                    v___x_3289_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3286_, 0, v___x_3289_);
                    v___x_3291_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
                    v___x_3291_ = v_reuseFailAlloc_3292_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3291_;
            }
            6 => {
                if v_isShared_3299_ == 0 {
                    v___x_3301_ = v___x_3298_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
                    v___x_3301_ = v_reuseFailAlloc_3302_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3301_;
            }
            8 => {
                if v_isShared_3307_ == 0 {
                    v___x_3309_ = v___x_3306_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
                    v___x_3309_ = v_reuseFailAlloc_3310_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3309_;
            }
            10 => {
                if v_isShared_3315_ == 0 {
                    v___x_3317_ = v___x_3314_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
                    v___x_3317_ = v_reuseFailAlloc_3318_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3317_;
            }
            12 => {
                if v_isShared_3328_ == 0 {
                    v___x_3330_ = v___x_3327_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
                    v___x_3330_ = v_reuseFailAlloc_3331_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3330_;
            }
            14 => {
                if v_isShared_3336_ == 0 {
                    v___x_3338_ = v___x_3335_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
                    v___x_3338_ = v_reuseFailAlloc_3339_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3338_;
            }
            16 => {
                return v___x_3343_;
            }
            17 => {
                if v_isShared_3349_ == 0 {
                    v___x_3351_ = v___x_3348_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
                    v___x_3351_ = v_reuseFailAlloc_3352_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3351_;
            }
            19 => {
                if v_isShared_3357_ == 0 {
                    v___x_3359_ = v___x_3356_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
                    v___x_3359_ = v_reuseFailAlloc_3360_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(
    mut v_type_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
    mut v_a_3372_: *mut crate::leanh::LeanObject,
    mut v_a_3373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
    crate::leanh::lean_dec(v_a_3372_);
    crate::leanh::lean_dec_ref(v_a_3371_);
    crate::leanh::lean_dec(v_a_3370_);
    crate::leanh::lean_dec_ref(v_a_3369_);
    crate::leanh::lean_dec(v_a_3368_);
    crate::leanh::lean_dec_ref(v_a_3367_);
    crate::leanh::lean_dec(v_a_3366_);
    crate::leanh::lean_dec_ref(v_a_3365_);
    crate::leanh::lean_dec(v_a_3364_);
    crate::leanh::lean_dec(v_a_3363_);
    return v_res_3374_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(
    mut v_00_u03b1_3375_: *mut crate::leanh::LeanObject,
    mut v_msg_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3388_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_3376_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
    return v___x_3388_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(
    mut v_00_u03b1_3389_: *mut crate::leanh::LeanObject,
    mut v_msg_3390_: *mut crate::leanh::LeanObject,
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
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_3389_, v_msg_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
    crate::leanh::lean_dec(v___y_3400_);
    crate::leanh::lean_dec_ref(v___y_3399_);
    crate::leanh::lean_dec(v___y_3398_);
    crate::leanh::lean_dec_ref(v___y_3397_);
    crate::leanh::lean_dec(v___y_3396_);
    crate::leanh::lean_dec_ref(v___y_3395_);
    crate::leanh::lean_dec(v___y_3394_);
    crate::leanh::lean_dec_ref(v___y_3393_);
    crate::leanh::lean_dec(v___y_3392_);
    crate::leanh::lean_dec(v___y_3391_);
    return v_res_3402_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(
    mut v_type_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
    mut v_s_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3419_: u8 = 0;
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3406_ = crate::leanh::lean_ctor_get(v_s_3405_, 0);
                v_typeIdOf_3407_ = crate::leanh::lean_ctor_get(v_s_3405_, 1);
                v_exprToRingId_3408_ = crate::leanh::lean_ctor_get(v_s_3405_, 2);
                v_semirings_3409_ = crate::leanh::lean_ctor_get(v_s_3405_, 3);
                v_stypeIdOf_3410_ = crate::leanh::lean_ctor_get(v_s_3405_, 4);
                v_exprToSemiringId_3411_ = crate::leanh::lean_ctor_get(v_s_3405_, 5);
                v_ncRings_3412_ = crate::leanh::lean_ctor_get(v_s_3405_, 6);
                v_exprToNCRingId_3413_ = crate::leanh::lean_ctor_get(v_s_3405_, 7);
                v_nctypeIdOf_3414_ = crate::leanh::lean_ctor_get(v_s_3405_, 8);
                v_ncSemirings_3415_ = crate::leanh::lean_ctor_get(v_s_3405_, 9);
                v_exprToNCSemiringId_3416_ = crate::leanh::lean_ctor_get(v_s_3405_, 10);
                v_ncstypeIdOf_3417_ = crate::leanh::lean_ctor_get(v_s_3405_, 11);
                v_steps_3418_ = crate::leanh::lean_ctor_get(v_s_3405_, 12);
                v_reportedMaxDegreeIssue_3419_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3427_ = (!crate::leanh::lean_is_exclusive(v_s_3405_)) as u8;
                if v_isSharedCheck_3427_ == 0 {
                    v___x_3421_ = v_s_3405_;
                    v_isShared_3422_ = v_isSharedCheck_3427_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_3418_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_3417_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_3416_);
                    crate::leanh::lean_inc(v_ncSemirings_3415_);
                    crate::leanh::lean_inc(v_nctypeIdOf_3414_);
                    crate::leanh::lean_inc(v_exprToNCRingId_3413_);
                    crate::leanh::lean_inc(v_ncRings_3412_);
                    crate::leanh::lean_inc(v_exprToSemiringId_3411_);
                    crate::leanh::lean_inc(v_stypeIdOf_3410_);
                    crate::leanh::lean_inc(v_semirings_3409_);
                    crate::leanh::lean_inc(v_exprToRingId_3408_);
                    crate::leanh::lean_inc(v_typeIdOf_3407_);
                    crate::leanh::lean_inc(v_rings_3406_);
                    crate::leanh::lean_dec(v_s_3405_);
                    v___x_3421_ = crate::leanh::lean_box(0);
                    v_isShared_3422_ = v_isSharedCheck_3427_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3423_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_3410_, v_type_3403_, v_a_3404_);
                if v_isShared_3422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3421_, 4, v___x_3423_);
                    v___x_3425_ = v___x_3421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_rings_3406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_typeIdOf_3407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_exprToRingId_3408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_semirings_3409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 4, v___x_3423_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3426_,
                        5,
                        v_exprToSemiringId_3411_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_ncRings_3412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_exprToNCRingId_3413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_nctypeIdOf_3414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 9, v_ncSemirings_3415_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3426_,
                        10,
                        v_exprToNCSemiringId_3416_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 11, v_ncstypeIdOf_3417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 12, v_steps_3418_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3426_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3419_,
                    );
                    v___x_3425_ = v_reuseFailAlloc_3426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
    mut v_type_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
    mut v_a_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v_stypeIdOf_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_isSharedCheck_3472_: u8 = 0;
    let mut v_a_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3440_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3429_, v_a_3437_);
                if crate::leanh::lean_obj_tag(v___x_3440_) == 0 {
                    v_a_3441_ = crate::leanh::lean_ctor_get(v___x_3440_, 0);
                    v_isSharedCheck_3472_ = (!crate::leanh::lean_is_exclusive(v___x_3440_)) as u8;
                    if v_isSharedCheck_3472_ == 0 {
                        v___x_3443_ = v___x_3440_;
                        v_isShared_3444_ = v_isSharedCheck_3472_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3441_);
                        crate::leanh::lean_dec(v___x_3440_);
                        v___x_3443_ = crate::leanh::lean_box(0);
                        v_isShared_3444_ = v_isSharedCheck_3472_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3428_);
                    v_a_3473_ = crate::leanh::lean_ctor_get(v___x_3440_, 0);
                    v_isSharedCheck_3480_ = (!crate::leanh::lean_is_exclusive(v___x_3440_)) as u8;
                    if v_isSharedCheck_3480_ == 0 {
                        v___x_3475_ = v___x_3440_;
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3473_);
                        crate::leanh::lean_dec(v___x_3440_);
                        v___x_3475_ = crate::leanh::lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_stypeIdOf_3445_ = crate::leanh::lean_ctor_get(v_a_3441_, 4);
                crate::leanh::lean_inc_ref(v_stypeIdOf_3445_);
                crate::leanh::lean_dec(v_a_3441_);
                v___x_3446_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_3445_, v_type_3428_);
                crate::leanh::lean_dec_ref(v_stypeIdOf_3445_);
                if crate::leanh::lean_obj_tag(v___x_3446_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_3428_);
                    v_val_3447_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                    crate::leanh::lean_inc(v_val_3447_);
                    crate::leanh::lean_dec_ref_known(v___x_3446_, 1);
                    if v_isShared_3444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3443_, 0, v_val_3447_);
                        v___x_3449_ = v___x_3443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_val_3447_);
                        v___x_3449_ = v_reuseFailAlloc_3450_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3446_);
                    crate::leanh::lean_del_object(v___x_3443_);
                    crate::leanh::lean_inc_ref(v_type_3428_);
                    v___x_3451_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
                    if crate::leanh::lean_obj_tag(v___x_3451_) == 0 {
                        v_a_3452_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                        crate::leanh::lean_inc_n(v_a_3452_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3451_, 1);
                        v___f_3453_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3453_, 0, v_type_3428_);
                        crate::leanh::lean_closure_set(v___f_3453_, 1, v_a_3452_);
                        v___x_3454_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3454_, v___f_3453_, v_a_3429_);
                        if crate::leanh::lean_obj_tag(v___x_3455_) == 0 {
                            v_isSharedCheck_3462_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3455_)) as u8;
                            if v_isSharedCheck_3462_ == 0 {
                                v_unused_3463_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                                crate::leanh::lean_dec(v_unused_3463_);
                                v___x_3457_ = v___x_3455_;
                                v_isShared_3458_ = v_isSharedCheck_3462_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3455_);
                                v___x_3457_ = crate::leanh::lean_box(0);
                                v_isShared_3458_ = v_isSharedCheck_3462_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3452_);
                            v_a_3464_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                            v_isSharedCheck_3471_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3455_)) as u8;
                            if v_isSharedCheck_3471_ == 0 {
                                v___x_3466_ = v___x_3455_;
                                v_isShared_3467_ = v_isSharedCheck_3471_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3464_);
                                crate::leanh::lean_dec(v___x_3455_);
                                v___x_3466_ = crate::leanh::lean_box(0);
                                v_isShared_3467_ = v_isSharedCheck_3471_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_3428_);
                        return v___x_3451_;
                    }
                }
            }
            2 => {
                return v___x_3449_;
            }
            3 => {
                if v_isShared_3458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3457_, 0, v_a_3452_);
                    v___x_3460_ = v___x_3457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3452_);
                    v___x_3460_ = v_reuseFailAlloc_3461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3460_;
            }
            5 => {
                if v_isShared_3467_ == 0 {
                    v___x_3469_ = v___x_3466_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
                    v___x_3469_ = v_reuseFailAlloc_3470_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3469_;
            }
            7 => {
                if v_isShared_3476_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(
    mut v_type_3481_: *mut crate::leanh::LeanObject,
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
    mut v_a_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
        v_type_3481_,
        v_a_3482_,
        v_a_3483_,
        v_a_3484_,
        v_a_3485_,
        v_a_3486_,
        v_a_3487_,
        v_a_3488_,
        v_a_3489_,
        v_a_3490_,
        v_a_3491_,
    );
    crate::leanh::lean_dec(v_a_3491_);
    crate::leanh::lean_dec_ref(v_a_3490_);
    crate::leanh::lean_dec(v_a_3489_);
    crate::leanh::lean_dec_ref(v_a_3488_);
    crate::leanh::lean_dec(v_a_3487_);
    crate::leanh::lean_dec_ref(v_a_3486_);
    crate::leanh::lean_dec(v_a_3485_);
    crate::leanh::lean_dec_ref(v_a_3484_);
    crate::leanh::lean_dec(v_a_3483_);
    crate::leanh::lean_dec(v_a_3482_);
    return v_res_3493_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(
    mut v___x_3494_: *mut crate::leanh::LeanObject,
    mut v_s_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3509_: u8 = 0;
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3496_ = crate::leanh::lean_ctor_get(v_s_3495_, 0);
                v_typeIdOf_3497_ = crate::leanh::lean_ctor_get(v_s_3495_, 1);
                v_exprToRingId_3498_ = crate::leanh::lean_ctor_get(v_s_3495_, 2);
                v_semirings_3499_ = crate::leanh::lean_ctor_get(v_s_3495_, 3);
                v_stypeIdOf_3500_ = crate::leanh::lean_ctor_get(v_s_3495_, 4);
                v_exprToSemiringId_3501_ = crate::leanh::lean_ctor_get(v_s_3495_, 5);
                v_ncRings_3502_ = crate::leanh::lean_ctor_get(v_s_3495_, 6);
                v_exprToNCRingId_3503_ = crate::leanh::lean_ctor_get(v_s_3495_, 7);
                v_nctypeIdOf_3504_ = crate::leanh::lean_ctor_get(v_s_3495_, 8);
                v_ncSemirings_3505_ = crate::leanh::lean_ctor_get(v_s_3495_, 9);
                v_exprToNCSemiringId_3506_ = crate::leanh::lean_ctor_get(v_s_3495_, 10);
                v_ncstypeIdOf_3507_ = crate::leanh::lean_ctor_get(v_s_3495_, 11);
                v_steps_3508_ = crate::leanh::lean_ctor_get(v_s_3495_, 12);
                v_reportedMaxDegreeIssue_3509_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3495_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3517_ = (!crate::leanh::lean_is_exclusive(v_s_3495_)) as u8;
                if v_isSharedCheck_3517_ == 0 {
                    v___x_3511_ = v_s_3495_;
                    v_isShared_3512_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_3508_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_3507_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_3506_);
                    crate::leanh::lean_inc(v_ncSemirings_3505_);
                    crate::leanh::lean_inc(v_nctypeIdOf_3504_);
                    crate::leanh::lean_inc(v_exprToNCRingId_3503_);
                    crate::leanh::lean_inc(v_ncRings_3502_);
                    crate::leanh::lean_inc(v_exprToSemiringId_3501_);
                    crate::leanh::lean_inc(v_stypeIdOf_3500_);
                    crate::leanh::lean_inc(v_semirings_3499_);
                    crate::leanh::lean_inc(v_exprToRingId_3498_);
                    crate::leanh::lean_inc(v_typeIdOf_3497_);
                    crate::leanh::lean_inc(v_rings_3496_);
                    crate::leanh::lean_dec(v_s_3495_);
                    v___x_3511_ = crate::leanh::lean_box(0);
                    v_isShared_3512_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3513_ = lean_array_push(v_ncSemirings_3505_, v___x_3494_);
                if v_isShared_3512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3511_, 9, v___x_3513_);
                    v___x_3515_ = v___x_3511_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_rings_3496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_typeIdOf_3497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_exprToRingId_3498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 3, v_semirings_3499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 4, v_stypeIdOf_3500_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3516_,
                        5,
                        v_exprToSemiringId_3501_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 6, v_ncRings_3502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 7, v_exprToNCRingId_3503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 8, v_nctypeIdOf_3504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 9, v___x_3513_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3516_,
                        10,
                        v_exprToNCSemiringId_3506_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 11, v_ncstypeIdOf_3507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 12, v_steps_3508_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3516_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3509_,
                    );
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(
    mut v_type_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v_val_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3566_: u8 = 0;
    let mut v_unused_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3575_: u8 = 0;
    let mut v_a_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_a_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_3523_);
                v___x_3530_ = l_Lean_Meta_getDecLevel(
                    v_type_3523_,
                    v_a_3525_,
                    v_a_3526_,
                    v_a_3527_,
                    v_a_3528_,
                );
                if crate::leanh::lean_obj_tag(v___x_3530_) == 0 {
                    v_a_3531_ = crate::leanh::lean_ctor_get(v___x_3530_, 0);
                    crate::leanh::lean_inc_n(v_a_3531_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3530_, 1);
                    v___x_3532_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1;
                    v___x_3533_ = crate::leanh::lean_box(0);
                    v___x_3534_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3534_, 0, v_a_3531_);
                    crate::leanh::lean_ctor_set(v___x_3534_, 1, v___x_3533_);
                    v___x_3535_ = l_Lean_mkConst(v___x_3532_, v___x_3534_);
                    crate::leanh::lean_inc_ref(v_type_3523_);
                    v___x_3536_ = l_Lean_Expr_app___override(v___x_3535_, v_type_3523_);
                    v___x_3537_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3536_,
                        v_a_3525_,
                        v_a_3526_,
                        v_a_3527_,
                        v_a_3528_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
                        v_a_3538_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3589_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v___x_3540_ = v___x_3537_;
                            v_isShared_3541_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3538_);
                            crate::leanh::lean_dec(v___x_3537_);
                            v___x_3540_ = crate::leanh::lean_box(0);
                            v_isShared_3541_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3531_);
                        crate::leanh::lean_dec_ref(v_type_3523_);
                        v_a_3590_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3597_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3597_ == 0 {
                            v___x_3592_ = v___x_3537_;
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3590_);
                            crate::leanh::lean_dec(v___x_3537_);
                            v___x_3592_ = crate::leanh::lean_box(0);
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3523_);
                    v_a_3598_ = crate::leanh::lean_ctor_get(v___x_3530_, 0);
                    v_isSharedCheck_3605_ = (!crate::leanh::lean_is_exclusive(v___x_3530_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3530_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3598_);
                        crate::leanh::lean_dec(v___x_3530_);
                        v___x_3600_ = crate::leanh::lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3538_) == 1 {
                    crate::leanh::lean_del_object(v___x_3540_);
                    v_val_3542_ = crate::leanh::lean_ctor_get(v_a_3538_, 0);
                    v_isSharedCheck_3584_ = (!crate::leanh::lean_is_exclusive(v_a_3538_)) as u8;
                    if v_isSharedCheck_3584_ == 0 {
                        v___x_3544_ = v_a_3538_;
                        v_isShared_3545_ = v_isSharedCheck_3584_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3542_);
                        crate::leanh::lean_dec(v_a_3538_);
                        v___x_3544_ = crate::leanh::lean_box(0);
                        v_isShared_3545_ = v_isSharedCheck_3584_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3538_);
                    crate::leanh::lean_dec(v_a_3531_);
                    crate::leanh::lean_dec_ref(v_type_3523_);
                    v___x_3585_ = crate::leanh::lean_box(0);
                    if v_isShared_3541_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3585_);
                        v___x_3587_ = v___x_3540_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
                        v___x_3587_ = v_reuseFailAlloc_3588_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3546_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3524_, v_a_3527_);
                if crate::leanh::lean_obj_tag(v___x_3546_) == 0 {
                    v_a_3547_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    crate::leanh::lean_inc(v_a_3547_);
                    crate::leanh::lean_dec_ref_known(v___x_3546_, 1);
                    v_ncSemirings_3548_ = crate::leanh::lean_ctor_get(v_a_3547_, 9);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3548_);
                    crate::leanh::lean_dec(v_a_3547_);
                    v___x_3549_ = lean_array_get_size(v_ncSemirings_3548_);
                    crate::leanh::lean_dec_ref(v_ncSemirings_3548_);
                    v___x_3550_ = crate::leanh::lean_box(0);
                    v___x_3551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
                    v___x_3552_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_3553_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3553_, 0, v___x_3549_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 1, v_type_3523_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 2, v_a_3531_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 3, v_val_3542_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 4, v___x_3550_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 5, v___x_3550_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 6, v___x_3550_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 7, v___x_3550_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 8, v___x_3551_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 9, v___x_3552_);
                    crate::leanh::lean_ctor_set(v___x_3553_, 10, v___x_3551_);
                    v___f_3554_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_3554_, 0, v___x_3553_);
                    v___x_3555_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3556_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3555_, v___f_3554_, v_a_3524_);
                    if crate::leanh::lean_obj_tag(v___x_3556_) == 0 {
                        v_isSharedCheck_3566_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                        if v_isSharedCheck_3566_ == 0 {
                            v_unused_3567_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                            crate::leanh::lean_dec(v_unused_3567_);
                            v___x_3558_ = v___x_3556_;
                            v_isShared_3559_ = v_isSharedCheck_3566_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3556_);
                            v___x_3558_ = crate::leanh::lean_box(0);
                            v_isShared_3559_ = v_isSharedCheck_3566_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3544_);
                        v_a_3568_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                        v_isSharedCheck_3575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                        if v_isSharedCheck_3575_ == 0 {
                            v___x_3570_ = v___x_3556_;
                            v_isShared_3571_ = v_isSharedCheck_3575_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3568_);
                            crate::leanh::lean_dec(v___x_3556_);
                            v___x_3570_ = crate::leanh::lean_box(0);
                            v_isShared_3571_ = v_isSharedCheck_3575_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3544_);
                    crate::leanh::lean_dec(v_val_3542_);
                    crate::leanh::lean_dec(v_a_3531_);
                    crate::leanh::lean_dec_ref(v_type_3523_);
                    v_a_3576_ = crate::leanh::lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3583_ = (!crate::leanh::lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3583_ == 0 {
                        v___x_3578_ = v___x_3546_;
                        v_isShared_3579_ = v_isSharedCheck_3583_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3576_);
                        crate::leanh::lean_dec(v___x_3546_);
                        v___x_3578_ = crate::leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3583_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3549_);
                    v___x_3561_ = v___x_3544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3549_);
                    v___x_3561_ = v_reuseFailAlloc_3565_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3558_, 0, v___x_3561_);
                    v___x_3563_ = v___x_3558_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
                    v___x_3563_ = v_reuseFailAlloc_3564_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3563_;
            }
            6 => {
                if v_isShared_3571_ == 0 {
                    v___x_3573_ = v___x_3570_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
                    v___x_3573_ = v_reuseFailAlloc_3574_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3573_;
            }
            8 => {
                if v_isShared_3579_ == 0 {
                    v___x_3581_ = v___x_3578_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
                    v___x_3581_ = v_reuseFailAlloc_3582_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3581_;
            }
            10 => {
                return v___x_3587_;
            }
            11 => {
                if v_isShared_3593_ == 0 {
                    v___x_3595_ = v___x_3592_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
                    v___x_3595_ = v_reuseFailAlloc_3596_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3595_;
            }
            13 => {
                if v_isShared_3601_ == 0 {
                    v___x_3603_ = v___x_3600_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(
    mut v_type_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
    mut v_a_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
    crate::leanh::lean_dec(v_a_3611_);
    crate::leanh::lean_dec_ref(v_a_3610_);
    crate::leanh::lean_dec(v_a_3609_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(
    mut v_type_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
    mut v_a_3617_: *mut crate::leanh::LeanObject,
    mut v_a_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
    mut v_a_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3614_, v_a_3615_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
    return v___x_3626_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(
    mut v_type_3627_: *mut crate::leanh::LeanObject,
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
    v_res_3639_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
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
    return v_res_3639_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(
    mut v_type_3640_: *mut crate::leanh::LeanObject,
    mut v_a_3641_: *mut crate::leanh::LeanObject,
    mut v_s_3642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3656_: u8 = 0;
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3643_ = crate::leanh::lean_ctor_get(v_s_3642_, 0);
                v_typeIdOf_3644_ = crate::leanh::lean_ctor_get(v_s_3642_, 1);
                v_exprToRingId_3645_ = crate::leanh::lean_ctor_get(v_s_3642_, 2);
                v_semirings_3646_ = crate::leanh::lean_ctor_get(v_s_3642_, 3);
                v_stypeIdOf_3647_ = crate::leanh::lean_ctor_get(v_s_3642_, 4);
                v_exprToSemiringId_3648_ = crate::leanh::lean_ctor_get(v_s_3642_, 5);
                v_ncRings_3649_ = crate::leanh::lean_ctor_get(v_s_3642_, 6);
                v_exprToNCRingId_3650_ = crate::leanh::lean_ctor_get(v_s_3642_, 7);
                v_nctypeIdOf_3651_ = crate::leanh::lean_ctor_get(v_s_3642_, 8);
                v_ncSemirings_3652_ = crate::leanh::lean_ctor_get(v_s_3642_, 9);
                v_exprToNCSemiringId_3653_ = crate::leanh::lean_ctor_get(v_s_3642_, 10);
                v_ncstypeIdOf_3654_ = crate::leanh::lean_ctor_get(v_s_3642_, 11);
                v_steps_3655_ = crate::leanh::lean_ctor_get(v_s_3642_, 12);
                v_reportedMaxDegreeIssue_3656_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3642_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3664_ = (!crate::leanh::lean_is_exclusive(v_s_3642_)) as u8;
                if v_isSharedCheck_3664_ == 0 {
                    v___x_3658_ = v_s_3642_;
                    v_isShared_3659_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_3655_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_3654_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_3653_);
                    crate::leanh::lean_inc(v_ncSemirings_3652_);
                    crate::leanh::lean_inc(v_nctypeIdOf_3651_);
                    crate::leanh::lean_inc(v_exprToNCRingId_3650_);
                    crate::leanh::lean_inc(v_ncRings_3649_);
                    crate::leanh::lean_inc(v_exprToSemiringId_3648_);
                    crate::leanh::lean_inc(v_stypeIdOf_3647_);
                    crate::leanh::lean_inc(v_semirings_3646_);
                    crate::leanh::lean_inc(v_exprToRingId_3645_);
                    crate::leanh::lean_inc(v_typeIdOf_3644_);
                    crate::leanh::lean_inc(v_rings_3643_);
                    crate::leanh::lean_dec(v_s_3642_);
                    v___x_3658_ = crate::leanh::lean_box(0);
                    v_isShared_3659_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3660_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_3654_, v_type_3640_, v_a_3641_);
                if v_isShared_3659_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3658_, 11, v___x_3660_);
                    v___x_3662_ = v___x_3658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_rings_3643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_typeIdOf_3644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_exprToRingId_3645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_semirings_3646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 4, v_stypeIdOf_3647_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3663_,
                        5,
                        v_exprToSemiringId_3648_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 6, v_ncRings_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 7, v_exprToNCRingId_3650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 8, v_nctypeIdOf_3651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 9, v_ncSemirings_3652_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3663_,
                        10,
                        v_exprToNCSemiringId_3653_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 11, v___x_3660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 12, v_steps_3655_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3663_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3656_,
                    );
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(
    mut v_type_3665_: *mut crate::leanh::LeanObject,
    mut v_a_3666_: *mut crate::leanh::LeanObject,
    mut v_a_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
    mut v_a_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v_ncstypeIdOf_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_unused_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3699_: u8 = 0;
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_a_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3672_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3666_, v_a_3669_);
                if crate::leanh::lean_obj_tag(v___x_3672_) == 0 {
                    v_a_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3704_ = (!crate::leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3704_ == 0 {
                        v___x_3675_ = v___x_3672_;
                        v_isShared_3676_ = v_isSharedCheck_3704_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3673_);
                        crate::leanh::lean_dec(v___x_3672_);
                        v___x_3675_ = crate::leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3704_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3665_);
                    v_a_3705_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3712_ = (!crate::leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3712_ == 0 {
                        v___x_3707_ = v___x_3672_;
                        v_isShared_3708_ = v_isSharedCheck_3712_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3705_);
                        crate::leanh::lean_dec(v___x_3672_);
                        v___x_3707_ = crate::leanh::lean_box(0);
                        v_isShared_3708_ = v_isSharedCheck_3712_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_ncstypeIdOf_3677_ = crate::leanh::lean_ctor_get(v_a_3673_, 11);
                crate::leanh::lean_inc_ref(v_ncstypeIdOf_3677_);
                crate::leanh::lean_dec(v_a_3673_);
                v___x_3678_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_3677_, v_type_3665_);
                crate::leanh::lean_dec_ref(v_ncstypeIdOf_3677_);
                if crate::leanh::lean_obj_tag(v___x_3678_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_3665_);
                    v_val_3679_ = crate::leanh::lean_ctor_get(v___x_3678_, 0);
                    crate::leanh::lean_inc(v_val_3679_);
                    crate::leanh::lean_dec_ref_known(v___x_3678_, 1);
                    if v_isShared_3676_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3675_, 0, v_val_3679_);
                        v___x_3681_ = v___x_3675_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_val_3679_);
                        v___x_3681_ = v_reuseFailAlloc_3682_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3678_);
                    crate::leanh::lean_del_object(v___x_3675_);
                    crate::leanh::lean_inc_ref(v_type_3665_);
                    v___x_3683_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
                    if crate::leanh::lean_obj_tag(v___x_3683_) == 0 {
                        v_a_3684_ = crate::leanh::lean_ctor_get(v___x_3683_, 0);
                        crate::leanh::lean_inc_n(v_a_3684_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3683_, 1);
                        v___f_3685_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_3685_, 0, v_type_3665_);
                        crate::leanh::lean_closure_set(v___f_3685_, 1, v_a_3684_);
                        v___x_3686_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3687_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3686_, v___f_3685_, v_a_3666_);
                        if crate::leanh::lean_obj_tag(v___x_3687_) == 0 {
                            v_isSharedCheck_3694_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3687_)) as u8;
                            if v_isSharedCheck_3694_ == 0 {
                                v_unused_3695_ = crate::leanh::lean_ctor_get(v___x_3687_, 0);
                                crate::leanh::lean_dec(v_unused_3695_);
                                v___x_3689_ = v___x_3687_;
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3687_);
                                v___x_3689_ = crate::leanh::lean_box(0);
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3684_);
                            v_a_3696_ = crate::leanh::lean_ctor_get(v___x_3687_, 0);
                            v_isSharedCheck_3703_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3687_)) as u8;
                            if v_isSharedCheck_3703_ == 0 {
                                v___x_3698_ = v___x_3687_;
                                v_isShared_3699_ = v_isSharedCheck_3703_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3696_);
                                crate::leanh::lean_dec(v___x_3687_);
                                v___x_3698_ = crate::leanh::lean_box(0);
                                v_isShared_3699_ = v_isSharedCheck_3703_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_3665_);
                        return v___x_3683_;
                    }
                }
            }
            2 => {
                return v___x_3681_;
            }
            3 => {
                if v_isShared_3690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v_a_3684_);
                    v___x_3692_ = v___x_3689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3684_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3692_;
            }
            5 => {
                if v_isShared_3699_ == 0 {
                    v___x_3701_ = v___x_3698_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
                    v___x_3701_ = v_reuseFailAlloc_3702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3701_;
            }
            7 => {
                if v_isShared_3708_ == 0 {
                    v___x_3710_ = v___x_3707_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
                    v___x_3710_ = v_reuseFailAlloc_3711_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(
    mut v_type_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3720_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(
        v_type_3713_,
        v_a_3714_,
        v_a_3715_,
        v_a_3716_,
        v_a_3717_,
        v_a_3718_,
    );
    crate::leanh::lean_dec(v_a_3718_);
    crate::leanh::lean_dec_ref(v_a_3717_);
    crate::leanh::lean_dec(v_a_3716_);
    crate::leanh::lean_dec_ref(v_a_3715_);
    crate::leanh::lean_dec(v_a_3714_);
    return v_res_3720_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(
    mut v_type_3721_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3733_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(
        v_type_3721_,
        v_a_3722_,
        v_a_3728_,
        v_a_3729_,
        v_a_3730_,
        v_a_3731_,
    );
    return v___x_3733_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(
    mut v_type_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
    mut v_a_3744_: *mut crate::leanh::LeanObject,
    mut v_a_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(
        v_type_3734_,
        v_a_3735_,
        v_a_3736_,
        v_a_3737_,
        v_a_3738_,
        v_a_3739_,
        v_a_3740_,
        v_a_3741_,
        v_a_3742_,
        v_a_3743_,
        v_a_3744_,
    );
    crate::leanh::lean_dec(v_a_3744_);
    crate::leanh::lean_dec_ref(v_a_3743_);
    crate::leanh::lean_dec(v_a_3742_);
    crate::leanh::lean_dec_ref(v_a_3741_);
    crate::leanh::lean_dec(v_a_3740_);
    crate::leanh::lean_dec_ref(v_a_3739_);
    crate::leanh::lean_dec(v_a_3738_);
    crate::leanh::lean_dec_ref(v_a_3737_);
    crate::leanh::lean_dec(v_a_3736_);
    crate::leanh::lean_dec(v_a_3735_);
    return v_res_3746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
}
