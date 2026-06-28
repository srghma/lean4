// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Tactic.Grind.Arith.Insts
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
};
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
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__4_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__5_value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__7_value) as *mut LeanObject,12221341192526463479 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut LeanObject,14047490016268445595 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__2_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__12_value) as *mut LeanObject,9499613419783151494 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__19_value) as *mut LeanObject,8615353994042975301 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__20_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [80, 111, 119, 73, 100, 101, 110, 116, 105, 116, 121, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__25_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 101, 119, 32, 114, 105, 110, 103, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut LeanObject,15814158821706329669 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_value) as *mut LeanObject,15814158821706329669 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__10_value) as *mut LeanObject,4308150853741380486 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [81, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__9_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_value) as *mut LeanObject,8254287559757149654 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__4_value) as *mut LeanObject,12174124158933200568 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [96, 103, 114, 105, 110, 100, 96, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 97, 105, 108, 117, 114, 101, 44, 32, 102, 97, 105, 108, 117, 114, 101, 32, 116, 111, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__0_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1874_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__0);
    v___x_1876_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(
    mut v_00_u03b2_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    v___x_1878_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0___closed__1);
    return v___x_1878_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(
    mut v___x_1882_: *mut LeanObject,
    mut v_____do__lift_1883_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v_options_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1896_: u8 = 0;
    v_options_1895_ = lean_ctor_get(v___y_1892_, 2);
    v_hasTrace_1896_ = lean_ctor_get_uint8(
        v_options_1895_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_1896_ == 0 {
        let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1882_);
        v___x_1897_ = lean_box((v_hasTrace_1896_) as usize);
        v___x_1898_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1898_, 0, v___x_1897_);
        return v___x_1898_;
    } else {
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: u8 = 0;
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
        v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1;
        v___x_1900_ = l_Lean_Name_append(v___x_1899_, v___x_1882_);
        v___x_1901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_1883_,
            v_options_1895_,
            v___x_1900_,
        );
        lean_dec(v___x_1900_);
        v___x_1902_ = lean_box((v___x_1901_) as usize);
        v___x_1903_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1903_, 0, v___x_1902_);
        return v___x_1903_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___boxed(
    mut v___x_1904_: *mut LeanObject,
    mut v_____do__lift_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_1904_, v_____do__lift_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
    lean_dec(v___y_1915_);
    lean_dec_ref(v___y_1914_);
    lean_dec(v___y_1913_);
    lean_dec_ref(v___y_1912_);
    lean_dec(v___y_1911_);
    lean_dec_ref(v___y_1910_);
    lean_dec(v___y_1909_);
    lean_dec_ref(v___y_1908_);
    lean_dec(v___y_1907_);
    lean_dec(v___y_1906_);
    lean_dec_ref(v_____do__lift_1905_);
    return v_res_1917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1(
    mut v___x_1918_: *mut LeanObject,
    mut v_s_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_1933_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_1920_ = lean_ctor_get(v_s_1919_, 0);
                v_typeIdOf_1921_ = lean_ctor_get(v_s_1919_, 1);
                v_exprToRingId_1922_ = lean_ctor_get(v_s_1919_, 2);
                v_semirings_1923_ = lean_ctor_get(v_s_1919_, 3);
                v_stypeIdOf_1924_ = lean_ctor_get(v_s_1919_, 4);
                v_exprToSemiringId_1925_ = lean_ctor_get(v_s_1919_, 5);
                v_ncRings_1926_ = lean_ctor_get(v_s_1919_, 6);
                v_exprToNCRingId_1927_ = lean_ctor_get(v_s_1919_, 7);
                v_nctypeIdOf_1928_ = lean_ctor_get(v_s_1919_, 8);
                v_ncSemirings_1929_ = lean_ctor_get(v_s_1919_, 9);
                v_exprToNCSemiringId_1930_ = lean_ctor_get(v_s_1919_, 10);
                v_ncstypeIdOf_1931_ = lean_ctor_get(v_s_1919_, 11);
                v_steps_1932_ = lean_ctor_get(v_s_1919_, 12);
                v_reportedMaxDegreeIssue_1933_ = lean_ctor_get_uint8(
                    v_s_1919_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_1941_ = (!lean_is_exclusive(v_s_1919_)) as u8;
                if v_isSharedCheck_1941_ == 0 {
                    v___x_1935_ = v_s_1919_;
                    v_isShared_1936_ = v_isSharedCheck_1941_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_1932_);
                    lean_inc(v_ncstypeIdOf_1931_);
                    lean_inc(v_exprToNCSemiringId_1930_);
                    lean_inc(v_ncSemirings_1929_);
                    lean_inc(v_nctypeIdOf_1928_);
                    lean_inc(v_exprToNCRingId_1927_);
                    lean_inc(v_ncRings_1926_);
                    lean_inc(v_exprToSemiringId_1925_);
                    lean_inc(v_stypeIdOf_1924_);
                    lean_inc(v_semirings_1923_);
                    lean_inc(v_exprToRingId_1922_);
                    lean_inc(v_typeIdOf_1921_);
                    lean_inc(v_rings_1920_);
                    lean_dec(v_s_1919_);
                    v___x_1935_ = lean_box(0);
                    v_isShared_1936_ = v_isSharedCheck_1941_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1937_ = lean_array_push(v_rings_1920_, v___x_1918_);
                if v_isShared_1936_ == 0 {
                    lean_ctor_set(v___x_1935_, 0, v___x_1937_);
                    v___x_1939_ = v___x_1935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_typeIdOf_1921_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_exprToRingId_1922_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_semirings_1923_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_stypeIdOf_1924_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 5, v_exprToSemiringId_1925_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_ncRings_1926_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_exprToNCRingId_1927_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_nctypeIdOf_1928_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 9, v_ncSemirings_1929_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 10, v_exprToNCSemiringId_1930_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 11, v_ncstypeIdOf_1931_);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 12, v_steps_1932_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1940_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_msgData_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_st_ref_get(v___y_1946_);
    v_env_1949_ = lean_ctor_get(v___x_1948_, 0);
    lean_inc_ref(v_env_1949_);
    lean_dec(v___x_1948_);
    v___x_1950_ = lean_st_ref_get(v___y_1944_);
    v_mctx_1951_ = lean_ctor_get(v___x_1950_, 0);
    lean_inc_ref(v_mctx_1951_);
    lean_dec(v___x_1950_);
    v_lctx_1952_ = lean_ctor_get(v___y_1943_, 2);
    v_options_1953_ = lean_ctor_get(v___y_1945_, 2);
    lean_inc_ref(v_options_1953_);
    lean_inc_ref(v_lctx_1952_);
    v___x_1954_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1954_, 0, v_env_1949_);
    lean_ctor_set(v___x_1954_, 1, v_mctx_1951_);
    lean_ctor_set(v___x_1954_, 2, v_lctx_1952_);
    lean_ctor_set(v___x_1954_, 3, v_options_1953_);
    v___x_1955_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1955_, 0, v___x_1954_);
    lean_ctor_set(v___x_1955_, 1, v_msgData_1942_);
    v___x_1956_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1956_, 0, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1___boxed(
    mut v_msgData_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msgData_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
    lean_dec(v___y_1961_);
    lean_dec_ref(v___y_1960_);
    lean_dec(v___y_1959_);
    lean_dec_ref(v___y_1958_);
    return v_res_1963_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: f64 = 0.0;
    v___x_1964_ = lean_unsigned_to_nat(0);
    v___x_1965_ = lean_float_of_nat(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(
    mut v_cls_1969_: *mut LeanObject,
    mut v_msg_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v_tid_1995_: u64 = 0;
    let mut v_traces_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: f64 = 0.0;
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1976_ = lean_ctor_get(v___y_1973_, 5);
                v___x_1977_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
                v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
                v_isSharedCheck_2022_ = (!lean_is_exclusive(v___x_1977_)) as u8;
                if v_isSharedCheck_2022_ == 0 {
                    v___x_1980_ = v___x_1977_;
                    v_isShared_1981_ = v_isSharedCheck_2022_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1978_);
                    lean_dec(v___x_1977_);
                    v___x_1980_ = lean_box(0);
                    v_isShared_1981_ = v_isSharedCheck_2022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1982_ = lean_st_ref_take(v___y_1974_);
                v_traceState_1983_ = lean_ctor_get(v___x_1982_, 4);
                v_env_1984_ = lean_ctor_get(v___x_1982_, 0);
                v_nextMacroScope_1985_ = lean_ctor_get(v___x_1982_, 1);
                v_ngen_1986_ = lean_ctor_get(v___x_1982_, 2);
                v_auxDeclNGen_1987_ = lean_ctor_get(v___x_1982_, 3);
                v_cache_1988_ = lean_ctor_get(v___x_1982_, 5);
                v_messages_1989_ = lean_ctor_get(v___x_1982_, 6);
                v_infoState_1990_ = lean_ctor_get(v___x_1982_, 7);
                v_snapshotTasks_1991_ = lean_ctor_get(v___x_1982_, 8);
                v_isSharedCheck_2021_ = (!lean_is_exclusive(v___x_1982_)) as u8;
                if v_isSharedCheck_2021_ == 0 {
                    v___x_1993_ = v___x_1982_;
                    v_isShared_1994_ = v_isSharedCheck_2021_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1991_);
                    lean_inc(v_infoState_1990_);
                    lean_inc(v_messages_1989_);
                    lean_inc(v_cache_1988_);
                    lean_inc(v_traceState_1983_);
                    lean_inc(v_auxDeclNGen_1987_);
                    lean_inc(v_ngen_1986_);
                    lean_inc(v_nextMacroScope_1985_);
                    lean_inc(v_env_1984_);
                    lean_dec(v___x_1982_);
                    v___x_1993_ = lean_box(0);
                    v_isShared_1994_ = v_isSharedCheck_2021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1995_ = lean_ctor_get_uint64(
                    v_traceState_1983_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_1996_ = lean_ctor_get(v_traceState_1983_, 0);
                v_isSharedCheck_2020_ = (!lean_is_exclusive(v_traceState_1983_)) as u8;
                if v_isSharedCheck_2020_ == 0 {
                    v___x_1998_ = v_traceState_1983_;
                    v_isShared_1999_ = v_isSharedCheck_2020_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_1996_);
                    lean_dec(v_traceState_1983_);
                    v___x_1998_ = lean_box(0);
                    v_isShared_1999_ = v_isSharedCheck_2020_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2000_ = lean_box(0);
                v___x_2001_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__0);
                v___x_2002_ = 0;
                v___x_2003_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__1;
                v___x_2004_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2004_, 0, v_cls_1969_);
                lean_ctor_set(v___x_2004_, 1, v___x_2000_);
                lean_ctor_set(v___x_2004_, 2, v___x_2003_);
                lean_ctor_set_float(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2001_,
                );
                lean_ctor_set_float(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2001_,
                );
                lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2002_,
                );
                v___x_2005_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg___closed__2;
                v___x_2006_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2006_, 0, v___x_2004_);
                lean_ctor_set(v___x_2006_, 1, v_a_1978_);
                lean_ctor_set(v___x_2006_, 2, v___x_2005_);
                lean_inc(v_ref_1976_);
                v___x_2007_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2007_, 0, v_ref_1976_);
                lean_ctor_set(v___x_2007_, 1, v___x_2006_);
                v___x_2008_ = l_Lean_PersistentArray_push___redArg(v_traces_1996_, v___x_2007_);
                if v_isShared_1999_ == 0 {
                    lean_ctor_set(v___x_1998_, 0, v___x_2008_);
                    v___x_2010_ = v___x_1998_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2008_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2019_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_1995_,
                    );
                    v___x_2010_ = v_reuseFailAlloc_2019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1994_ == 0 {
                    lean_ctor_set(v___x_1993_, 4, v___x_2010_);
                    v___x_2012_ = v___x_1993_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_env_1984_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_nextMacroScope_1985_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_ngen_1986_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_auxDeclNGen_1987_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 4, v___x_2010_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_cache_1988_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_messages_1989_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_infoState_1990_);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_snapshotTasks_1991_);
                    v___x_2012_ = v_reuseFailAlloc_2018_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2013_ = lean_st_ref_set(v___y_1974_, v___x_2012_);
                v___x_2014_ = lean_box(0);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set(v___x_1980_, 0, v___x_2014_);
                    v___x_2016_ = v___x_1980_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
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
    mut v_cls_2023_: *mut LeanObject,
    mut v_msg_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_2023_, v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
    lean_dec(v___y_2028_);
    lean_dec_ref(v___y_2027_);
    lean_dec(v___y_2026_);
    lean_dec_ref(v___y_2025_);
    return v_res_2030_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14()
-> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v___x_2062_ = lean_unsigned_to_nat(32);
    v___x_2063_ = lean_mk_empty_array_with_capacity(v___x_2062_);
    v___x_2064_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    return v___x_2064_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15()
-> *mut LeanObject {
    let mut v___x_2065_: usize = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = 5usize;
    v___x_2066_ = lean_unsigned_to_nat(0);
    v___x_2067_ = lean_unsigned_to_nat(32);
    v___x_2068_ = lean_mk_empty_array_with_capacity(v___x_2067_);
    v___x_2069_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__14);
    v___x_2070_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2070_, 0, v___x_2069_);
    lean_ctor_set(v___x_2070_, 1, v___x_2068_);
    lean_ctor_set(v___x_2070_, 2, v___x_2066_);
    lean_ctor_set(v___x_2070_, 3, v___x_2066_);
    lean_ctor_set_usize(v___x_2070_, 4, v___x_2065_);
    return v___x_2070_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16()
-> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17()
-> *mut LeanObject {
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    v___x_2072_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__16);
    v___x_2073_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2073_, 0, v___x_2072_);
    return v___x_2073_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18()
-> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__0(lean_box(0));
    return v___x_2074_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21()
-> *mut LeanObject {
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6;
    v___x_2081_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0___closed__1;
    v___x_2082_ = l_Lean_Name_append(v___x_2081_, v___x_2080_);
    return v___x_2082_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23()
-> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    v___x_2084_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__22;
    v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
    return v___x_2085_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27()
-> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__26;
    v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29()
-> *mut LeanObject {
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__28;
    v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
    return v___x_2093_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(
    mut v_type_2094_: *mut LeanObject,
    mut v_a_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v_val_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v_inheritedTraceOptions_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_unused_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v___y_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_reuseFailAlloc_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2239_: u8 = 0;
    let mut v_a_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_a_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2260_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_a_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut v___y_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v___y_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_a_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut v_isSharedCheck_2369_: u8 = 0;
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_a_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_a_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2094_);
                v___x_2106_ = l_Lean_Meta_getDecLevel(
                    v_type_2094_,
                    v_a_2101_,
                    v_a_2102_,
                    v_a_2103_,
                    v_a_2104_,
                );
                if lean_obj_tag(v___x_2106_) == 0 {
                    v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
                    lean_inc_n(v_a_2107_, 2);
                    lean_dec_ref_known(v___x_2106_, 1);
                    v___x_2108_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__3;
                    v___x_2109_ = lean_box(0);
                    v___x_2110_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2110_, 0, v_a_2107_);
                    lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                    lean_inc_ref(v___x_2110_);
                    v___x_2111_ = l_Lean_mkConst(v___x_2108_, v___x_2110_);
                    lean_inc_ref(v_type_2094_);
                    v___x_2112_ = l_Lean_Expr_app___override(v___x_2111_, v_type_2094_);
                    v___x_2113_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2112_,
                        v_a_2101_,
                        v_a_2102_,
                        v_a_2103_,
                        v_a_2104_,
                    );
                    if lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
                        v_isSharedCheck_2375_ = (!lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2375_ == 0 {
                            v___x_2116_ = v___x_2113_;
                            v_isShared_2117_ = v_isSharedCheck_2375_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2114_);
                            lean_dec(v___x_2113_);
                            v___x_2116_ = lean_box(0);
                            v_isShared_2117_ = v_isSharedCheck_2375_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2110_, 2);
                        lean_dec(v_a_2107_);
                        lean_dec_ref(v_type_2094_);
                        v_a_2376_ = lean_ctor_get(v___x_2113_, 0);
                        v_isSharedCheck_2383_ = (!lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2383_ == 0 {
                            v___x_2378_ = v___x_2113_;
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 38;
                            continue;
                        } else {
                            lean_inc(v_a_2376_);
                            lean_dec(v___x_2113_);
                            v___x_2378_ = lean_box(0);
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2094_);
                    v_a_2384_ = lean_ctor_get(v___x_2106_, 0);
                    v_isSharedCheck_2391_ = (!lean_is_exclusive(v___x_2106_)) as u8;
                    if v_isSharedCheck_2391_ == 0 {
                        v___x_2386_ = v___x_2106_;
                        v_isShared_2387_ = v_isSharedCheck_2391_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_2384_);
                        lean_dec(v___x_2106_);
                        v___x_2386_ = lean_box(0);
                        v_isShared_2387_ = v_isSharedCheck_2391_;
                        state = 40;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2114_) == 1 {
                    lean_del_object(v___x_2116_);
                    v_val_2118_ = lean_ctor_get(v_a_2114_, 0);
                    v_isSharedCheck_2370_ = (!lean_is_exclusive(v_a_2114_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2120_ = v_a_2114_;
                        v_isShared_2121_ = v_isSharedCheck_2370_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2118_);
                        lean_dec(v_a_2114_);
                        v___x_2120_ = lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2370_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2114_);
                    lean_dec_ref_known(v___x_2110_, 2);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v___x_2371_ = lean_box(0);
                    if v_isShared_2117_ == 0 {
                        lean_ctor_set(v___x_2116_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2116_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 37;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2122_ = lean_ctor_get(v_a_2103_, 13);
                v___x_2123_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__6;
                v___x_2124_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_2123_, v_inheritedTraceOptions_2122_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
                v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
                v_isSharedCheck_2369_ = (!lean_is_exclusive(v___x_2124_)) as u8;
                if v_isSharedCheck_2369_ == 0 {
                    v___x_2127_ = v___x_2124_;
                    v_isShared_2128_ = v_isSharedCheck_2369_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_2125_);
                    lean_dec(v___x_2124_);
                    v___x_2127_ = lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2369_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2129_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__8;
                lean_inc_ref_n(v___x_2110_, 3);
                v___x_2130_ = l_Lean_mkConst(v___x_2129_, v___x_2110_);
                lean_inc(v_val_2118_);
                lean_inc_ref_n(v_type_2094_, 3);
                v___x_2131_ = l_Lean_mkAppB(v___x_2130_, v_type_2094_, v_val_2118_);
                v___x_2132_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11;
                v___x_2133_ = l_Lean_mkConst(v___x_2132_, v___x_2110_);
                lean_inc_ref(v___x_2131_);
                v___x_2134_ = l_Lean_mkAppB(v___x_2133_, v_type_2094_, v___x_2131_);
                v___x_2135_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__13;
                v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2110_);
                lean_inc_ref(v___x_2134_);
                v___x_2137_ = l_Lean_mkAppB(v___x_2136_, v_type_2094_, v___x_2134_);
                v___x_2347_ = (lean_unbox(v_a_2125_) as u8);
                lean_dec(v_a_2125_);
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
                    if lean_obj_tag(v___x_2348_) == 0 {
                        lean_dec_ref_known(v___x_2348_, 1);
                        v___x_2349_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
                        lean_inc_ref(v_type_2094_);
                        v___x_2350_ = l_Lean_MessageData_ofExpr(v_type_2094_);
                        v___x_2351_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2351_, 0, v___x_2349_);
                        lean_ctor_set(v___x_2351_, 1, v___x_2350_);
                        v___x_2352_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2351_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
                        if lean_obj_tag(v___x_2352_) == 0 {
                            lean_dec_ref_known(v___x_2352_, 1);
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
                            lean_dec_ref(v___x_2137_);
                            lean_dec_ref(v___x_2134_);
                            lean_dec_ref(v___x_2131_);
                            lean_del_object(v___x_2127_);
                            lean_del_object(v___x_2120_);
                            lean_dec(v_val_2118_);
                            lean_dec_ref_known(v___x_2110_, 2);
                            lean_dec(v_a_2107_);
                            lean_dec_ref(v_type_2094_);
                            v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
                            v_isSharedCheck_2360_ = (!lean_is_exclusive(v___x_2352_)) as u8;
                            if v_isSharedCheck_2360_ == 0 {
                                v___x_2355_ = v___x_2352_;
                                v_isShared_2356_ = v_isSharedCheck_2360_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_2353_);
                                lean_dec(v___x_2352_);
                                v___x_2355_ = lean_box(0);
                                v_isShared_2356_ = v_isSharedCheck_2360_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2137_);
                        lean_dec_ref(v___x_2134_);
                        lean_dec_ref(v___x_2131_);
                        lean_del_object(v___x_2127_);
                        lean_del_object(v___x_2120_);
                        lean_dec(v_val_2118_);
                        lean_dec_ref_known(v___x_2110_, 2);
                        lean_dec(v_a_2107_);
                        lean_dec_ref(v_type_2094_);
                        v_a_2361_ = lean_ctor_get(v___x_2348_, 0);
                        v_isSharedCheck_2368_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                        if v_isSharedCheck_2368_ == 0 {
                            v___x_2363_ = v___x_2348_;
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 35;
                            continue;
                        } else {
                            lean_inc(v_a_2361_);
                            lean_dec(v___x_2348_);
                            v___x_2363_ = lean_box(0);
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
                if lean_obj_tag(v___x_2145_) == 0 {
                    v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
                    lean_inc(v_a_2146_);
                    lean_dec_ref_known(v___x_2145_, 1);
                    v_rings_2147_ = lean_ctor_get(v_a_2146_, 0);
                    lean_inc_ref(v_rings_2147_);
                    lean_dec(v_a_2146_);
                    v___x_2148_ = lean_box(0);
                    v___x_2149_ = lean_array_get_size(v_rings_2147_);
                    lean_dec_ref(v_rings_2147_);
                    v___x_2150_ = lean_unsigned_to_nat(0);
                    v___x_2151_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_2152_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
                    v___x_2153_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v___x_2153_, 0, v___x_2149_);
                    lean_ctor_set(v___x_2153_, 1, v_type_2094_);
                    lean_ctor_set(v___x_2153_, 2, v_a_2107_);
                    lean_ctor_set(v___x_2153_, 3, v___x_2131_);
                    lean_ctor_set(v___x_2153_, 4, v___x_2134_);
                    lean_ctor_set(v___x_2153_, 5, v___y_2142_);
                    lean_ctor_set(v___x_2153_, 6, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 7, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 8, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 9, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 10, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 11, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 12, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 13, v___x_2148_);
                    lean_ctor_set(v___x_2153_, 14, v___x_2151_);
                    lean_ctor_set(v___x_2153_, 15, v___x_2152_);
                    lean_ctor_set(v___x_2153_, 16, v___x_2152_);
                    v___x_2154_ = lean_box(1);
                    v___x_2155_ = 0;
                    v___x_2156_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__18);
                    v___x_2157_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v___x_2157_, 0, v___x_2153_);
                    lean_ctor_set(v___x_2157_, 1, v___x_2148_);
                    lean_ctor_set(v___x_2157_, 2, v___x_2148_);
                    lean_ctor_set(v___x_2157_, 3, v___x_2137_);
                    lean_ctor_set(v___x_2157_, 4, v_val_2118_);
                    lean_ctor_set(v___x_2157_, 5, v___y_2139_);
                    lean_ctor_set(v___x_2157_, 6, v___y_2141_);
                    lean_ctor_set(v___x_2157_, 7, v___y_2140_);
                    lean_ctor_set(v___x_2157_, 8, v___x_2151_);
                    lean_ctor_set(v___x_2157_, 9, v___x_2150_);
                    lean_ctor_set(v___x_2157_, 10, v___x_2150_);
                    lean_ctor_set(v___x_2157_, 11, v___x_2154_);
                    lean_ctor_set(v___x_2157_, 12, v___x_2109_);
                    lean_ctor_set(v___x_2157_, 13, v___x_2151_);
                    lean_ctor_set(v___x_2157_, 14, v___x_2156_);
                    lean_ctor_set(v___x_2157_, 15, v___x_2150_);
                    lean_ctor_set(v___x_2157_, 16, v___x_2148_);
                    lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v___x_2155_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2157_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                        v___x_2155_,
                    );
                    v___f_2158_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__1 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_2158_, 0, v___x_2157_);
                    v___x_2159_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_2160_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2159_, v___f_2158_, v___y_2143_);
                    if lean_obj_tag(v___x_2160_) == 0 {
                        v_isSharedCheck_2170_ = (!lean_is_exclusive(v___x_2160_)) as u8;
                        if v_isSharedCheck_2170_ == 0 {
                            v_unused_2171_ = lean_ctor_get(v___x_2160_, 0);
                            lean_dec(v_unused_2171_);
                            v___x_2162_ = v___x_2160_;
                            v_isShared_2163_ = v_isSharedCheck_2170_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_2160_);
                            v___x_2162_ = lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2170_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2120_);
                        v_a_2172_ = lean_ctor_get(v___x_2160_, 0);
                        v_isSharedCheck_2179_ = (!lean_is_exclusive(v___x_2160_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v___x_2174_ = v___x_2160_;
                            v_isShared_2175_ = v_isSharedCheck_2179_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2172_);
                            lean_dec(v___x_2160_);
                            v___x_2174_ = lean_box(0);
                            v_isShared_2175_ = v_isSharedCheck_2179_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2142_);
                    lean_dec(v___y_2141_);
                    lean_dec(v___y_2140_);
                    lean_dec(v___y_2139_);
                    lean_dec_ref(v___x_2137_);
                    lean_dec_ref(v___x_2134_);
                    lean_dec_ref(v___x_2131_);
                    lean_del_object(v___x_2120_);
                    lean_dec(v_val_2118_);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v_a_2180_ = lean_ctor_get(v___x_2145_, 0);
                    v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2145_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2182_ = v___x_2145_;
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2180_);
                        lean_dec(v___x_2145_);
                        v___x_2182_ = lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2121_ == 0 {
                    lean_ctor_set(v___x_2120_, 0, v___x_2149_);
                    v___x_2165_ = v___x_2120_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2149_);
                    v___x_2165_ = v_reuseFailAlloc_2169_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2163_ == 0 {
                    lean_ctor_set(v___x_2162_, 0, v___x_2165_);
                    v___x_2167_ = v___x_2162_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
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
                    v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2185_;
            }
            12 => {
                lean_inc_ref(v___y_2204_);
                if v_isShared_2128_ == 0 {
                    lean_ctor_set_tag(v___x_2127_, 3);
                    lean_ctor_set(v___x_2127_, 0, v___y_2204_);
                    v___x_2206_ = v___x_2127_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___y_2204_);
                    v___x_2206_ = v_reuseFailAlloc_2218_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2207_ = l_Lean_MessageData_ofFormat(v___x_2206_);
                lean_inc_ref(v___y_2202_);
                v___x_2208_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2208_, 0, v___y_2202_);
                lean_ctor_set(v___x_2208_, 1, v___x_2207_);
                v___x_2209_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2208_, v___y_2191_, v___y_2194_, v___y_2203_, v___y_2192_);
                if lean_obj_tag(v___x_2209_) == 0 {
                    lean_dec_ref_known(v___x_2209_, 1);
                    v___y_2139_ = v___y_2193_;
                    v___y_2140_ = v___y_2200_;
                    v___y_2141_ = v___y_2196_;
                    v___y_2142_ = v___y_2197_;
                    v___y_2143_ = v___y_2198_;
                    v___y_2144_ = v___y_2203_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_2200_);
                    lean_dec(v___y_2197_);
                    lean_dec(v___y_2196_);
                    lean_dec(v___y_2193_);
                    lean_dec_ref(v___x_2137_);
                    lean_dec_ref(v___x_2134_);
                    lean_dec_ref(v___x_2131_);
                    lean_del_object(v___x_2120_);
                    lean_dec(v_val_2118_);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
                    v_isSharedCheck_2217_ = (!lean_is_exclusive(v___x_2209_)) as u8;
                    if v_isSharedCheck_2217_ == 0 {
                        v___x_2212_ = v___x_2209_;
                        v_isShared_2213_ = v_isSharedCheck_2217_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2210_);
                        lean_dec(v___x_2209_);
                        v___x_2212_ = lean_box(0);
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
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
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
                lean_inc_ref(v_type_2094_);
                v___x_2234_ = l_Lean_Expr_app___override(v___x_2233_, v_type_2094_);
                v___x_2235_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_2234_,
                    v___y_2228_,
                    v___y_2229_,
                    v___y_2230_,
                    v___y_2231_,
                );
                if lean_obj_tag(v___x_2235_) == 0 {
                    v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
                    lean_inc(v_a_2236_);
                    lean_dec_ref_known(v___x_2235_, 1);
                    lean_inc_ref(v_type_2094_);
                    lean_inc(v_a_2107_);
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
                    if lean_obj_tag(v___x_2237_) == 0 {
                        v_options_2238_ = lean_ctor_get(v___y_2230_, 2);
                        v_hasTrace_2239_ = lean_ctor_get_uint8(
                            v_options_2238_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2239_ == 0 {
                            lean_del_object(v___x_2127_);
                            v_a_2240_ = lean_ctor_get(v___x_2237_, 0);
                            lean_inc(v_a_2240_);
                            lean_dec_ref_known(v___x_2237_, 1);
                            v___y_2139_ = v___y_2220_;
                            v___y_2140_ = v_a_2240_;
                            v___y_2141_ = v_a_2236_;
                            v___y_2142_ = v___y_2221_;
                            v___y_2143_ = v___y_2222_;
                            v___y_2144_ = v___y_2230_;
                            state = 4;
                            continue;
                        } else {
                            v_a_2241_ = lean_ctor_get(v___x_2237_, 0);
                            lean_inc(v_a_2241_);
                            lean_dec_ref_known(v___x_2237_, 1);
                            v_inheritedTraceOptions_2242_ = lean_ctor_get(v___y_2230_, 13);
                            v___x_2243_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
                            v___x_2244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2242_,
                                v_options_2238_,
                                v___x_2243_,
                            );
                            if v___x_2244_ == 0 {
                                lean_del_object(v___x_2127_);
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
                                if lean_obj_tag(v___x_2245_) == 0 {
                                    lean_dec_ref_known(v___x_2245_, 1);
                                    v___x_2246_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__23);
                                    if lean_obj_tag(v_a_2241_) == 0 {
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
                                    lean_dec(v_a_2241_);
                                    lean_dec(v_a_2236_);
                                    lean_dec(v___y_2221_);
                                    lean_dec(v___y_2220_);
                                    lean_dec_ref(v___x_2137_);
                                    lean_dec_ref(v___x_2134_);
                                    lean_dec_ref(v___x_2131_);
                                    lean_del_object(v___x_2127_);
                                    lean_del_object(v___x_2120_);
                                    lean_dec(v_val_2118_);
                                    lean_dec(v_a_2107_);
                                    lean_dec_ref(v_type_2094_);
                                    v_a_2249_ = lean_ctor_get(v___x_2245_, 0);
                                    v_isSharedCheck_2256_ = (!lean_is_exclusive(v___x_2245_)) as u8;
                                    if v_isSharedCheck_2256_ == 0 {
                                        v___x_2251_ = v___x_2245_;
                                        v_isShared_2252_ = v_isSharedCheck_2256_;
                                        state = 17;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2249_);
                                        lean_dec(v___x_2245_);
                                        v___x_2251_ = lean_box(0);
                                        v_isShared_2252_ = v_isSharedCheck_2256_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2236_);
                        lean_dec(v___y_2221_);
                        lean_dec(v___y_2220_);
                        lean_dec_ref(v___x_2137_);
                        lean_dec_ref(v___x_2134_);
                        lean_dec_ref(v___x_2131_);
                        lean_del_object(v___x_2127_);
                        lean_del_object(v___x_2120_);
                        lean_dec(v_val_2118_);
                        lean_dec(v_a_2107_);
                        lean_dec_ref(v_type_2094_);
                        v_a_2257_ = lean_ctor_get(v___x_2237_, 0);
                        v_isSharedCheck_2264_ = (!lean_is_exclusive(v___x_2237_)) as u8;
                        if v_isSharedCheck_2264_ == 0 {
                            v___x_2259_ = v___x_2237_;
                            v_isShared_2260_ = v_isSharedCheck_2264_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_2257_);
                            lean_dec(v___x_2237_);
                            v___x_2259_ = lean_box(0);
                            v_isShared_2260_ = v_isSharedCheck_2264_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2221_);
                    lean_dec(v___y_2220_);
                    lean_dec_ref(v___x_2137_);
                    lean_dec_ref(v___x_2134_);
                    lean_dec_ref(v___x_2131_);
                    lean_del_object(v___x_2127_);
                    lean_del_object(v___x_2120_);
                    lean_dec(v_val_2118_);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v_a_2265_ = lean_ctor_get(v___x_2235_, 0);
                    v_isSharedCheck_2272_ = (!lean_is_exclusive(v___x_2235_)) as u8;
                    if v_isSharedCheck_2272_ == 0 {
                        v___x_2267_ = v___x_2235_;
                        v_isShared_2268_ = v_isSharedCheck_2272_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_2265_);
                        lean_dec(v___x_2235_);
                        v___x_2267_ = lean_box(0);
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
                    v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
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
                    v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
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
                    v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2270_;
            }
            23 => {
                lean_inc_ref(v___y_2287_);
                v___x_2288_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2288_, 0, v___y_2287_);
                v___x_2289_ = l_Lean_MessageData_ofFormat(v___x_2288_);
                lean_inc_ref(v___y_2274_);
                v___x_2290_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2290_, 0, v___y_2274_);
                lean_ctor_set(v___x_2290_, 1, v___x_2289_);
                v___x_2291_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2123_, v___x_2290_, v___y_2285_, v___y_2282_, v___y_2275_, v___y_2277_);
                if lean_obj_tag(v___x_2291_) == 0 {
                    lean_dec_ref_known(v___x_2291_, 1);
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
                    lean_dec(v___y_2281_);
                    lean_dec(v___y_2276_);
                    lean_dec_ref(v___x_2137_);
                    lean_dec_ref(v___x_2134_);
                    lean_dec_ref(v___x_2131_);
                    lean_del_object(v___x_2127_);
                    lean_del_object(v___x_2120_);
                    lean_dec(v_val_2118_);
                    lean_dec_ref_known(v___x_2110_, 2);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
                    v_isSharedCheck_2299_ = (!lean_is_exclusive(v___x_2291_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v___x_2294_ = v___x_2291_;
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_2292_);
                        lean_dec(v___x_2291_);
                        v___x_2294_ = lean_box(0);
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
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2297_;
            }
            26 => {
                lean_inc_ref(v___x_2134_);
                lean_inc_ref(v_type_2094_);
                lean_inc(v_a_2107_);
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
                if lean_obj_tag(v___x_2311_) == 0 {
                    v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
                    lean_inc(v_a_2312_);
                    lean_dec_ref_known(v___x_2311_, 1);
                    lean_inc_ref(v_type_2094_);
                    lean_inc(v_a_2107_);
                    v___x_2313_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
                        v_a_2107_,
                        v_type_2094_,
                        v___y_2307_,
                        v___y_2308_,
                        v___y_2309_,
                        v___y_2310_,
                    );
                    if lean_obj_tag(v___x_2313_) == 0 {
                        v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
                        lean_inc(v_a_2314_);
                        lean_dec_ref_known(v___x_2313_, 1);
                        v_inheritedTraceOptions_2315_ = lean_ctor_get(v___y_2309_, 13);
                        v___x_2316_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___lam__0(v___x_2123_, v_inheritedTraceOptions_2315_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
                        v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
                        lean_inc(v_a_2317_);
                        lean_dec_ref(v___x_2316_);
                        v___x_2318_ = (lean_unbox(v_a_2317_) as u8);
                        lean_dec(v_a_2317_);
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
                            if lean_obj_tag(v___x_2319_) == 0 {
                                lean_dec_ref_known(v___x_2319_, 1);
                                v___x_2320_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__27);
                                if lean_obj_tag(v_a_2314_) == 0 {
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
                                lean_dec(v_a_2314_);
                                lean_dec(v_a_2312_);
                                lean_dec_ref(v___x_2137_);
                                lean_dec_ref(v___x_2134_);
                                lean_dec_ref(v___x_2131_);
                                lean_del_object(v___x_2127_);
                                lean_del_object(v___x_2120_);
                                lean_dec(v_val_2118_);
                                lean_dec_ref_known(v___x_2110_, 2);
                                lean_dec(v_a_2107_);
                                lean_dec_ref(v_type_2094_);
                                v_a_2323_ = lean_ctor_get(v___x_2319_, 0);
                                v_isSharedCheck_2330_ = (!lean_is_exclusive(v___x_2319_)) as u8;
                                if v_isSharedCheck_2330_ == 0 {
                                    v___x_2325_ = v___x_2319_;
                                    v_isShared_2326_ = v_isSharedCheck_2330_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_2323_);
                                    lean_dec(v___x_2319_);
                                    v___x_2325_ = lean_box(0);
                                    v_isShared_2326_ = v_isSharedCheck_2330_;
                                    state = 27;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2312_);
                        lean_dec_ref(v___x_2137_);
                        lean_dec_ref(v___x_2134_);
                        lean_dec_ref(v___x_2131_);
                        lean_del_object(v___x_2127_);
                        lean_del_object(v___x_2120_);
                        lean_dec(v_val_2118_);
                        lean_dec_ref_known(v___x_2110_, 2);
                        lean_dec(v_a_2107_);
                        lean_dec_ref(v_type_2094_);
                        v_a_2331_ = lean_ctor_get(v___x_2313_, 0);
                        v_isSharedCheck_2338_ = (!lean_is_exclusive(v___x_2313_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2313_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_2331_);
                            lean_dec(v___x_2313_);
                            v___x_2333_ = lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2137_);
                    lean_dec_ref(v___x_2134_);
                    lean_dec_ref(v___x_2131_);
                    lean_del_object(v___x_2127_);
                    lean_del_object(v___x_2120_);
                    lean_dec(v_val_2118_);
                    lean_dec_ref_known(v___x_2110_, 2);
                    lean_dec(v_a_2107_);
                    lean_dec_ref(v_type_2094_);
                    v_a_2339_ = lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2346_ = (!lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2346_ == 0 {
                        v___x_2341_ = v___x_2311_;
                        v_isShared_2342_ = v_isSharedCheck_2346_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_2339_);
                        lean_dec(v___x_2311_);
                        v___x_2341_ = lean_box(0);
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
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
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
                    v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
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
                    v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
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
                    v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
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
                    v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
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
                    v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
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
                    v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
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
    mut v_type_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
    mut v_a_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2404_: *mut LeanObject = core::ptr::null_mut();
    v_res_2404_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
    lean_dec(v_a_2402_);
    lean_dec_ref(v_a_2401_);
    lean_dec(v_a_2400_);
    lean_dec_ref(v_a_2399_);
    lean_dec(v_a_2398_);
    lean_dec_ref(v_a_2397_);
    lean_dec(v_a_2396_);
    lean_dec_ref(v_a_2395_);
    lean_dec(v_a_2394_);
    lean_dec(v_a_2393_);
    return v_res_2404_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(
    mut v_cls_2405_: *mut LeanObject,
    mut v_msg_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v_cls_2405_, v_msg_2406_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    return v___x_2418_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___boxed(
    mut v_cls_2419_: *mut LeanObject,
    mut v_msg_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2432_: *mut LeanObject = core::ptr::null_mut();
    v_res_2432_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1(v_cls_2419_, v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
    lean_dec(v___y_2430_);
    lean_dec_ref(v___y_2429_);
    lean_dec(v___y_2428_);
    lean_dec_ref(v___y_2427_);
    lean_dec(v___y_2426_);
    lean_dec_ref(v___y_2425_);
    lean_dec(v___y_2424_);
    lean_dec_ref(v___y_2423_);
    lean_dec(v___y_2422_);
    lean_dec(v___y_2421_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
    mut v_x_2435_: *mut LeanObject,
    mut v_x_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2437_ = lean_ctor_get(v_x_2433_, 0);
                v_vs_2438_ = lean_ctor_get(v_x_2433_, 1);
                v_isSharedCheck_2462_ = (!lean_is_exclusive(v_x_2433_)) as u8;
                if v_isSharedCheck_2462_ == 0 {
                    v___x_2440_ = v_x_2433_;
                    v_isShared_2441_ = v_isSharedCheck_2462_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2438_);
                    lean_inc(v_ks_2437_);
                    lean_dec(v_x_2433_);
                    v___x_2440_ = lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2462_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2442_ = lean_array_get_size(v_ks_2437_);
                v___x_2443_ = lean_nat_dec_lt(v_x_2434_, v___x_2442_);
                if v___x_2443_ == 0 {
                    lean_dec(v_x_2434_);
                    v___x_2444_ = lean_array_push(v_ks_2437_, v_x_2435_);
                    v___x_2445_ = lean_array_push(v_vs_2438_, v_x_2436_);
                    if v_isShared_2441_ == 0 {
                        lean_ctor_set(v___x_2440_, 1, v___x_2445_);
                        lean_ctor_set(v___x_2440_, 0, v___x_2444_);
                        v___x_2447_ = v___x_2440_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2444_);
                        lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2445_);
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
                            v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_ks_2437_);
                            lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_vs_2438_);
                            v___x_2452_ = v_reuseFailAlloc_2456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2457_ = lean_array_fset(v_ks_2437_, v_x_2434_, v_x_2435_);
                        v___x_2458_ = lean_array_fset(v_vs_2438_, v_x_2434_, v_x_2436_);
                        lean_dec(v_x_2434_);
                        if v_isShared_2441_ == 0 {
                            lean_ctor_set(v___x_2440_, 1, v___x_2458_);
                            lean_ctor_set(v___x_2440_, 0, v___x_2457_);
                            v___x_2460_ = v___x_2440_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2457_);
                            lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2458_);
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
                v___x_2453_ = lean_unsigned_to_nat(1);
                v___x_2454_ = lean_nat_add(v_x_2434_, v___x_2453_);
                lean_dec(v_x_2434_);
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
    mut v_n_2463_: *mut LeanObject,
    mut v_k_2464_: *mut LeanObject,
    mut v_v_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2466_ = lean_unsigned_to_nat(0);
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
    v___x_2472_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_2473_ = lean_usize_sub(v___x_2472_, v___x_2471_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2474_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(
    mut v_x_2475_: *mut LeanObject,
    mut v_x_2476_: usize,
    mut v_x_2477_: usize,
    mut v_x_2478_: *mut LeanObject,
    mut v_x_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: usize = 0;
    let mut v___x_2482_: usize = 0;
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v_j_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v_v_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_node_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2516_: usize = 0;
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2524_: u8 = 0;
    let mut v_unused_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: u8 = 0;
    let mut v_ks_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: usize = 0;
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v_reuseFailAlloc_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2475_) == 0 {
                    v_es_2480_ = lean_ctor_get(v_x_2475_, 0);
                    v___x_2481_ = 5usize;
                    v___x_2482_ = 1usize;
                    v___x_2483_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2484_ = lean_usize_land(v_x_2476_, v___x_2483_);
                    v_j_2485_ = lean_usize_to_nat(v___x_2484_);
                    v___x_2486_ = lean_array_get_size(v_es_2480_);
                    v___x_2487_ = lean_nat_dec_lt(v_j_2485_, v___x_2486_);
                    if v___x_2487_ == 0 {
                        lean_dec(v_j_2485_);
                        lean_dec(v_x_2479_);
                        lean_dec_ref(v_x_2478_);
                        return v_x_2475_;
                    } else {
                        lean_inc_ref(v_es_2480_);
                        v_isSharedCheck_2524_ = (!lean_is_exclusive(v_x_2475_)) as u8;
                        if v_isSharedCheck_2524_ == 0 {
                            v_unused_2525_ = lean_ctor_get(v_x_2475_, 0);
                            lean_dec(v_unused_2525_);
                            v___x_2489_ = v_x_2475_;
                            v_isShared_2490_ = v_isSharedCheck_2524_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2475_);
                            v___x_2489_ = lean_box(0);
                            v_isShared_2490_ = v_isSharedCheck_2524_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2526_ = lean_ctor_get(v_x_2475_, 0);
                    v_vs_2527_ = lean_ctor_get(v_x_2475_, 1);
                    v_isSharedCheck_2547_ = (!lean_is_exclusive(v_x_2475_)) as u8;
                    if v_isSharedCheck_2547_ == 0 {
                        v___x_2529_ = v_x_2475_;
                        v_isShared_2530_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2527_);
                        lean_inc(v_ks_2526_);
                        lean_dec(v_x_2475_);
                        v___x_2529_ = lean_box(0);
                        v_isShared_2530_ = v_isSharedCheck_2547_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2491_ = lean_array_fget(v_es_2480_, v_j_2485_);
                v___x_2492_ = lean_box(0);
                v_xs_x27_2493_ = lean_array_fset(v_es_2480_, v_j_2485_, v___x_2492_);
                match lean_obj_tag(v_v_2491_) {
                    0 => {
                        v_key_2500_ = lean_ctor_get(v_v_2491_, 0);
                        v_val_2501_ = lean_ctor_get(v_v_2491_, 1);
                        v_isSharedCheck_2511_ = (!lean_is_exclusive(v_v_2491_)) as u8;
                        if v_isSharedCheck_2511_ == 0 {
                            v___x_2503_ = v_v_2491_;
                            v_isShared_2504_ = v_isSharedCheck_2511_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2501_);
                            lean_inc(v_key_2500_);
                            lean_dec(v_v_2491_);
                            v___x_2503_ = lean_box(0);
                            v_isShared_2504_ = v_isSharedCheck_2511_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2512_ = lean_ctor_get(v_v_2491_, 0);
                        v_isSharedCheck_2522_ = (!lean_is_exclusive(v_v_2491_)) as u8;
                        if v_isSharedCheck_2522_ == 0 {
                            v___x_2514_ = v_v_2491_;
                            v_isShared_2515_ = v_isSharedCheck_2522_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2512_);
                            lean_dec(v_v_2491_);
                            v___x_2514_ = lean_box(0);
                            v_isShared_2515_ = v_isSharedCheck_2522_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2523_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2523_, 0, v_x_2478_);
                        lean_ctor_set(v___x_2523_, 1, v_x_2479_);
                        v___y_2495_ = v___x_2523_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2496_ = lean_array_fset(v_xs_x27_2493_, v_j_2485_, v___y_2495_);
                lean_dec(v_j_2485_);
                if v_isShared_2490_ == 0 {
                    lean_ctor_set(v___x_2489_, 0, v___x_2496_);
                    v___x_2498_ = v___x_2489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
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
                    lean_del_object(v___x_2503_);
                    v___x_2506_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2500_,
                        v_val_2501_,
                        v_x_2478_,
                        v_x_2479_,
                    );
                    v___x_2507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2507_, 0, v___x_2506_);
                    v___y_2495_ = v___x_2507_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2501_);
                    lean_dec(v_key_2500_);
                    if v_isShared_2504_ == 0 {
                        lean_ctor_set(v___x_2503_, 1, v_x_2479_);
                        lean_ctor_set(v___x_2503_, 0, v_x_2478_);
                        v___x_2509_ = v___x_2503_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_x_2478_);
                        lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_x_2479_);
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
                    lean_ctor_set(v___x_2514_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2514_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
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
                    v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_ks_2526_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_vs_2527_);
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
                    v___x_2544_ = lean_unsigned_to_nat(4);
                    v___x_2545_ = lean_nat_dec_lt(v___x_2543_, v___x_2544_);
                    lean_dec(v___x_2543_);
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
                    v_ks_2536_ = lean_ctor_get(v_newNode_2533_, 0);
                    lean_inc_ref(v_ks_2536_);
                    v_vs_2537_ = lean_ctor_get(v_newNode_2533_, 1);
                    lean_inc_ref(v_vs_2537_);
                    lean_dec_ref(v_newNode_2533_);
                    v___x_2538_ = lean_unsigned_to_nat(0);
                    v___x_2539_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_2540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_2477_, v_ks_2536_, v_vs_2537_, v___x_2538_, v___x_2539_);
                    lean_dec_ref(v_vs_2537_);
                    lean_dec_ref(v_ks_2536_);
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
    mut v_keys_2549_: *mut LeanObject,
    mut v_vals_2550_: *mut LeanObject,
    mut v_i_2551_: *mut LeanObject,
    mut v_entries_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v_k_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: u64 = 0;
    let mut v_h_2558_: usize = 0;
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v_h_2564_: usize = 0;
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2553_ = lean_array_get_size(v_keys_2549_);
                v___x_2554_ = lean_nat_dec_lt(v_i_2551_, v___x_2553_);
                if v___x_2554_ == 0 {
                    lean_dec(v_i_2551_);
                    return v_entries_2552_;
                } else {
                    v_k_2555_ = lean_array_fget_borrowed(v_keys_2549_, v_i_2551_);
                    v_v_2556_ = lean_array_fget_borrowed(v_vals_2550_, v_i_2551_);
                    v___x_2557_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2555_);
                    v_h_2558_ = lean_uint64_to_usize(v___x_2557_);
                    v___x_2559_ = 5usize;
                    v___x_2560_ = lean_unsigned_to_nat(1);
                    v___x_2561_ = 1usize;
                    v___x_2562_ = lean_usize_sub(v_depth_2548_, v___x_2561_);
                    v___x_2563_ = lean_usize_mul(v___x_2559_, v___x_2562_);
                    v_h_2564_ = lean_usize_shift_right(v_h_2558_, v___x_2563_);
                    v___x_2565_ = lean_nat_add(v_i_2551_, v___x_2560_);
                    lean_dec(v_i_2551_);
                    lean_inc(v_v_2556_);
                    lean_inc(v_k_2555_);
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
    mut v_depth_2568_: *mut LeanObject,
    mut v_keys_2569_: *mut LeanObject,
    mut v_vals_2570_: *mut LeanObject,
    mut v_i_2571_: *mut LeanObject,
    mut v_entries_2572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2573_: usize = 0;
    let mut v_res_2574_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2573_ = lean_unbox_usize(v_depth_2568_);
    lean_dec(v_depth_2568_);
    v_res_2574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2573_, v_keys_2569_, v_vals_2570_, v_i_2571_, v_entries_2572_);
    lean_dec_ref(v_vals_2570_);
    lean_dec_ref(v_keys_2569_);
    return v_res_2574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_2575_: *mut LeanObject,
    mut v_x_2576_: *mut LeanObject,
    mut v_x_2577_: *mut LeanObject,
    mut v_x_2578_: *mut LeanObject,
    mut v_x_2579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3692__boxed_2580_: usize = 0;
    let mut v_x_3693__boxed_2581_: usize = 0;
    let mut v_res_2582_: *mut LeanObject = core::ptr::null_mut();
    v_x_3692__boxed_2580_ = lean_unbox_usize(v_x_2576_);
    lean_dec(v_x_2576_);
    v_x_3693__boxed_2581_ = lean_unbox_usize(v_x_2577_);
    lean_dec(v_x_2577_);
    v_res_2582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2575_, v_x_3692__boxed_2580_, v_x_3693__boxed_2581_, v_x_2578_, v_x_2579_);
    return v_res_2582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(
    mut v_x_2583_: *mut LeanObject,
    mut v_x_2584_: *mut LeanObject,
    mut v_x_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2584_);
    v___x_2587_ = lean_uint64_to_usize(v___x_2586_);
    v___x_2588_ = 1usize;
    v___x_2589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2583_, v___x_2587_, v___x_2588_, v_x_2584_, v_x_2585_);
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(
    mut v_type_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_s_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2606_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2593_ = lean_ctor_get(v_s_2592_, 0);
                v_typeIdOf_2594_ = lean_ctor_get(v_s_2592_, 1);
                v_exprToRingId_2595_ = lean_ctor_get(v_s_2592_, 2);
                v_semirings_2596_ = lean_ctor_get(v_s_2592_, 3);
                v_stypeIdOf_2597_ = lean_ctor_get(v_s_2592_, 4);
                v_exprToSemiringId_2598_ = lean_ctor_get(v_s_2592_, 5);
                v_ncRings_2599_ = lean_ctor_get(v_s_2592_, 6);
                v_exprToNCRingId_2600_ = lean_ctor_get(v_s_2592_, 7);
                v_nctypeIdOf_2601_ = lean_ctor_get(v_s_2592_, 8);
                v_ncSemirings_2602_ = lean_ctor_get(v_s_2592_, 9);
                v_exprToNCSemiringId_2603_ = lean_ctor_get(v_s_2592_, 10);
                v_ncstypeIdOf_2604_ = lean_ctor_get(v_s_2592_, 11);
                v_steps_2605_ = lean_ctor_get(v_s_2592_, 12);
                v_reportedMaxDegreeIssue_2606_ = lean_ctor_get_uint8(
                    v_s_2592_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2614_ = (!lean_is_exclusive(v_s_2592_)) as u8;
                if v_isSharedCheck_2614_ == 0 {
                    v___x_2608_ = v_s_2592_;
                    v_isShared_2609_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_2605_);
                    lean_inc(v_ncstypeIdOf_2604_);
                    lean_inc(v_exprToNCSemiringId_2603_);
                    lean_inc(v_ncSemirings_2602_);
                    lean_inc(v_nctypeIdOf_2601_);
                    lean_inc(v_exprToNCRingId_2600_);
                    lean_inc(v_ncRings_2599_);
                    lean_inc(v_exprToSemiringId_2598_);
                    lean_inc(v_stypeIdOf_2597_);
                    lean_inc(v_semirings_2596_);
                    lean_inc(v_exprToRingId_2595_);
                    lean_inc(v_typeIdOf_2594_);
                    lean_inc(v_rings_2593_);
                    lean_dec(v_s_2592_);
                    v___x_2608_ = lean_box(0);
                    v_isShared_2609_ = v_isSharedCheck_2614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2610_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_2594_, v_type_2590_, v_a_2591_);
                if v_isShared_2609_ == 0 {
                    lean_ctor_set(v___x_2608_, 1, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_rings_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2610_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_exprToRingId_2595_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_semirings_2596_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_stypeIdOf_2597_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 5, v_exprToSemiringId_2598_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_ncRings_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_exprToNCRingId_2600_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_nctypeIdOf_2601_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 9, v_ncSemirings_2602_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 10, v_exprToNCSemiringId_2603_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 11, v_ncstypeIdOf_2604_);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 12, v_steps_2605_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2613_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_keys_2615_: *mut LeanObject,
    mut v_vals_2616_: *mut LeanObject,
    mut v_i_2617_: *mut LeanObject,
    mut v_k_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: u8 = 0;
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2619_ = lean_array_get_size(v_keys_2615_);
                v___x_2620_ = lean_nat_dec_lt(v_i_2617_, v___x_2619_);
                if v___x_2620_ == 0 {
                    lean_dec(v_i_2617_);
                    v___x_2621_ = lean_box(0);
                    return v___x_2621_;
                } else {
                    v_k_x27_2622_ = lean_array_fget_borrowed(v_keys_2615_, v_i_2617_);
                    v___x_2623_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2618_,
                            v_k_x27_2622_,
                        );
                    if v___x_2623_ == 0 {
                        v___x_2624_ = lean_unsigned_to_nat(1);
                        v___x_2625_ = lean_nat_add(v_i_2617_, v___x_2624_);
                        lean_dec(v_i_2617_);
                        v_i_2617_ = v___x_2625_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2627_ = lean_array_fget_borrowed(v_vals_2616_, v_i_2617_);
                        lean_dec(v_i_2617_);
                        lean_inc(v___x_2627_);
                        v___x_2628_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2628_, 0, v___x_2627_);
                        return v___x_2628_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2629_: *mut LeanObject,
    mut v_vals_2630_: *mut LeanObject,
    mut v_i_2631_: *mut LeanObject,
    mut v_k_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2633_: *mut LeanObject = core::ptr::null_mut();
    v_res_2633_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2629_, v_vals_2630_, v_i_2631_, v_k_2632_);
    lean_dec_ref(v_k_2632_);
    lean_dec_ref(v_vals_2630_);
    lean_dec_ref(v_keys_2629_);
    return v_res_2633_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(
    mut v_x_2634_: *mut LeanObject,
    mut v_x_2635_: usize,
    mut v_x_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: usize = 0;
    let mut v_j_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: usize = 0;
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2634_) == 0 {
                    v_es_2637_ = lean_ctor_get(v_x_2634_, 0);
                    v___x_2638_ = lean_box(2);
                    v___x_2639_ = 5usize;
                    v___x_2640_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2641_ = lean_usize_land(v_x_2635_, v___x_2640_);
                    v_j_2642_ = lean_usize_to_nat(v___x_2641_);
                    v___x_2643_ = lean_array_get_borrowed(v___x_2638_, v_es_2637_, v_j_2642_);
                    lean_dec(v_j_2642_);
                    match lean_obj_tag(v___x_2643_) {
                        0 => {
                            v_key_2644_ = lean_ctor_get(v___x_2643_, 0);
                            v_val_2645_ = lean_ctor_get(v___x_2643_, 1);
                            v___x_2646_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2636_, v_key_2644_);
                            if v___x_2646_ == 0 {
                                v___x_2647_ = lean_box(0);
                                return v___x_2647_;
                            } else {
                                lean_inc(v_val_2645_);
                                v___x_2648_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2648_, 0, v_val_2645_);
                                return v___x_2648_;
                            }
                        }
                        1 => {
                            v_node_2649_ = lean_ctor_get(v___x_2643_, 0);
                            v___x_2650_ = lean_usize_shift_right(v_x_2635_, v___x_2639_);
                            v_x_2634_ = v_node_2649_;
                            v_x_2635_ = v___x_2650_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2652_ = lean_box(0);
                            return v___x_2652_;
                        }
                    }
                } else {
                    v_ks_2653_ = lean_ctor_get(v_x_2634_, 0);
                    v_vs_2654_ = lean_ctor_get(v_x_2634_, 1);
                    v___x_2655_ = lean_unsigned_to_nat(0);
                    v___x_2656_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2653_, v_vs_2654_, v___x_2655_, v_x_2636_);
                    return v___x_2656_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2657_: *mut LeanObject,
    mut v_x_2658_: *mut LeanObject,
    mut v_x_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3910__boxed_2660_: usize = 0;
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_x_3910__boxed_2660_ = lean_unbox_usize(v_x_2658_);
    lean_dec(v_x_2658_);
    v_res_2661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2657_, v_x_3910__boxed_2660_, v_x_2659_);
    lean_dec_ref(v_x_2659_);
    lean_dec_ref(v_x_2657_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(
    mut v_x_2662_: *mut LeanObject,
    mut v_x_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2664_: u64 = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2663_);
    v___x_2665_ = lean_uint64_to_usize(v___x_2664_);
    v___x_2666_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2662_, v___x_2665_, v_x_2663_);
    return v___x_2666_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(
    mut v_x_2667_: *mut LeanObject,
    mut v_x_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_2667_, v_x_2668_);
    lean_dec_ref(v_x_2668_);
    lean_dec_ref(v_x_2667_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
    mut v_type_2670_: *mut LeanObject,
    mut v_a_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
    mut v_a_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v_typeIdOf_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_unused_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
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
                v___x_2682_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2671_, v_a_2679_);
                if lean_obj_tag(v___x_2682_) == 0 {
                    v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
                    v_isSharedCheck_2714_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2714_ == 0 {
                        v___x_2685_ = v___x_2682_;
                        v_isShared_2686_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2683_);
                        lean_dec(v___x_2682_);
                        v___x_2685_ = lean_box(0);
                        v_isShared_2686_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2670_);
                    v_a_2715_ = lean_ctor_get(v___x_2682_, 0);
                    v_isSharedCheck_2722_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v___x_2717_ = v___x_2682_;
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2715_);
                        lean_dec(v___x_2682_);
                        v___x_2717_ = lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_typeIdOf_2687_ = lean_ctor_get(v_a_2683_, 1);
                lean_inc_ref(v_typeIdOf_2687_);
                lean_dec(v_a_2683_);
                v___x_2688_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_2687_, v_type_2670_);
                lean_dec_ref(v_typeIdOf_2687_);
                if lean_obj_tag(v___x_2688_) == 1 {
                    lean_dec_ref(v_type_2670_);
                    v_val_2689_ = lean_ctor_get(v___x_2688_, 0);
                    lean_inc(v_val_2689_);
                    lean_dec_ref_known(v___x_2688_, 1);
                    if v_isShared_2686_ == 0 {
                        lean_ctor_set(v___x_2685_, 0, v_val_2689_);
                        v___x_2691_ = v___x_2685_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_val_2689_);
                        v___x_2691_ = v_reuseFailAlloc_2692_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2688_);
                    lean_del_object(v___x_2685_);
                    lean_inc_ref(v_type_2670_);
                    v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
                    if lean_obj_tag(v___x_2693_) == 0 {
                        v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
                        lean_inc_n(v_a_2694_, 2);
                        lean_dec_ref_known(v___x_2693_, 1);
                        v___f_2695_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_2695_, 0, v_type_2670_);
                        lean_closure_set(v___f_2695_, 1, v_a_2694_);
                        v___x_2696_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_2697_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2696_, v___f_2695_, v_a_2671_);
                        if lean_obj_tag(v___x_2697_) == 0 {
                            v_isSharedCheck_2704_ = (!lean_is_exclusive(v___x_2697_)) as u8;
                            if v_isSharedCheck_2704_ == 0 {
                                v_unused_2705_ = lean_ctor_get(v___x_2697_, 0);
                                lean_dec(v_unused_2705_);
                                v___x_2699_ = v___x_2697_;
                                v_isShared_2700_ = v_isSharedCheck_2704_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2697_);
                                v___x_2699_ = lean_box(0);
                                v_isShared_2700_ = v_isSharedCheck_2704_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2694_);
                            v_a_2706_ = lean_ctor_get(v___x_2697_, 0);
                            v_isSharedCheck_2713_ = (!lean_is_exclusive(v___x_2697_)) as u8;
                            if v_isSharedCheck_2713_ == 0 {
                                v___x_2708_ = v___x_2697_;
                                v_isShared_2709_ = v_isSharedCheck_2713_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2706_);
                                lean_dec(v___x_2697_);
                                v___x_2708_ = lean_box(0);
                                v_isShared_2709_ = v_isSharedCheck_2713_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_2670_);
                        return v___x_2693_;
                    }
                }
            }
            2 => {
                return v___x_2691_;
            }
            3 => {
                if v_isShared_2700_ == 0 {
                    lean_ctor_set(v___x_2699_, 0, v_a_2694_);
                    v___x_2702_ = v___x_2699_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2694_);
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
            7 => {
                if v_isShared_2718_ == 0 {
                    v___x_2720_ = v___x_2717_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
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
    mut v_type_2723_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2733_);
    lean_dec_ref(v_a_2732_);
    lean_dec(v_a_2731_);
    lean_dec_ref(v_a_2730_);
    lean_dec(v_a_2729_);
    lean_dec_ref(v_a_2728_);
    lean_dec(v_a_2727_);
    lean_dec_ref(v_a_2726_);
    lean_dec(v_a_2725_);
    lean_dec(v_a_2724_);
    return v_res_2735_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(
    mut v_00_u03b2_2736_: *mut LeanObject,
    mut v_x_2737_: *mut LeanObject,
    mut v_x_2738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    v___x_2739_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_2737_, v_x_2738_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(
    mut v_00_u03b2_2740_: *mut LeanObject,
    mut v_x_2741_: *mut LeanObject,
    mut v_x_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2743_: *mut LeanObject = core::ptr::null_mut();
    v_res_2743_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_2740_, v_x_2741_, v_x_2742_);
    lean_dec_ref(v_x_2742_);
    lean_dec_ref(v_x_2741_);
    return v_res_2743_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(
    mut v_00_u03b2_2744_: *mut LeanObject,
    mut v_x_2745_: *mut LeanObject,
    mut v_x_2746_: *mut LeanObject,
    mut v_x_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    v___x_2748_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_2745_, v_x_2746_, v_x_2747_);
    return v___x_2748_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(
    mut v_00_u03b2_2749_: *mut LeanObject,
    mut v_x_2750_: *mut LeanObject,
    mut v_x_2751_: usize,
    mut v_x_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_2750_, v_x_2751_, v_x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2754_: *mut LeanObject,
    mut v_x_2755_: *mut LeanObject,
    mut v_x_2756_: *mut LeanObject,
    mut v_x_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4072__boxed_2758_: usize = 0;
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
    v_x_4072__boxed_2758_ = lean_unbox_usize(v_x_2756_);
    lean_dec(v_x_2756_);
    v_res_2759_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_2754_, v_x_2755_, v_x_4072__boxed_2758_, v_x_2757_);
    lean_dec_ref(v_x_2757_);
    lean_dec_ref(v_x_2755_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(
    mut v_00_u03b2_2760_: *mut LeanObject,
    mut v_x_2761_: *mut LeanObject,
    mut v_x_2762_: usize,
    mut v_x_2763_: usize,
    mut v_x_2764_: *mut LeanObject,
    mut v_x_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_2761_, v_x_2762_, v_x_2763_, v_x_2764_, v_x_2765_);
    return v___x_2766_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2767_: *mut LeanObject,
    mut v_x_2768_: *mut LeanObject,
    mut v_x_2769_: *mut LeanObject,
    mut v_x_2770_: *mut LeanObject,
    mut v_x_2771_: *mut LeanObject,
    mut v_x_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4083__boxed_2773_: usize = 0;
    let mut v_x_4084__boxed_2774_: usize = 0;
    let mut v_res_2775_: *mut LeanObject = core::ptr::null_mut();
    v_x_4083__boxed_2773_ = lean_unbox_usize(v_x_2769_);
    lean_dec(v_x_2769_);
    v_x_4084__boxed_2774_ = lean_unbox_usize(v_x_2770_);
    lean_dec(v_x_2770_);
    v_res_2775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_2767_, v_x_2768_, v_x_4083__boxed_2773_, v_x_4084__boxed_2774_, v_x_2771_, v_x_2772_);
    return v_res_2775_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2776_: *mut LeanObject,
    mut v_keys_2777_: *mut LeanObject,
    mut v_vals_2778_: *mut LeanObject,
    mut v_heq_2779_: *mut LeanObject,
    mut v_i_2780_: *mut LeanObject,
    mut v_k_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v___x_2782_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2777_, v_vals_2778_, v_i_2780_, v_k_2781_);
    return v___x_2782_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2783_: *mut LeanObject,
    mut v_keys_2784_: *mut LeanObject,
    mut v_vals_2785_: *mut LeanObject,
    mut v_heq_2786_: *mut LeanObject,
    mut v_i_2787_: *mut LeanObject,
    mut v_k_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2789_: *mut LeanObject = core::ptr::null_mut();
    v_res_2789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2783_, v_keys_2784_, v_vals_2785_, v_heq_2786_, v_i_2787_, v_k_2788_);
    lean_dec_ref(v_k_2788_);
    lean_dec_ref(v_vals_2785_);
    lean_dec_ref(v_keys_2784_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2790_: *mut LeanObject,
    mut v_n_2791_: *mut LeanObject,
    mut v_k_2792_: *mut LeanObject,
    mut v_v_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_2791_, v_k_2792_, v_v_2793_);
    return v___x_2794_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2795_: *mut LeanObject,
    mut v_depth_2796_: usize,
    mut v_keys_2797_: *mut LeanObject,
    mut v_vals_2798_: *mut LeanObject,
    mut v_heq_2799_: *mut LeanObject,
    mut v_i_2800_: *mut LeanObject,
    mut v_entries_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    v___x_2802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2796_, v_keys_2797_, v_vals_2798_, v_i_2800_, v_entries_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2803_: *mut LeanObject,
    mut v_depth_2804_: *mut LeanObject,
    mut v_keys_2805_: *mut LeanObject,
    mut v_vals_2806_: *mut LeanObject,
    mut v_heq_2807_: *mut LeanObject,
    mut v_i_2808_: *mut LeanObject,
    mut v_entries_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2810_: usize = 0;
    let mut v_res_2811_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2810_ = lean_unbox_usize(v_depth_2804_);
    lean_dec(v_depth_2804_);
    v_res_2811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2803_, v_depth_boxed_2810_, v_keys_2805_, v_vals_2806_, v_heq_2807_, v_i_2808_, v_entries_2809_);
    lean_dec_ref(v_vals_2806_);
    lean_dec_ref(v_keys_2805_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2812_: *mut LeanObject,
    mut v_x_2813_: *mut LeanObject,
    mut v_x_2814_: *mut LeanObject,
    mut v_x_2815_: *mut LeanObject,
    mut v_x_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2813_, v_x_2814_, v_x_2815_, v_x_2816_);
    return v___x_2817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(
    mut v___x_2818_: *mut LeanObject,
    mut v_s_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2833_: u8 = 0;
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2820_ = lean_ctor_get(v_s_2819_, 0);
                v_typeIdOf_2821_ = lean_ctor_get(v_s_2819_, 1);
                v_exprToRingId_2822_ = lean_ctor_get(v_s_2819_, 2);
                v_semirings_2823_ = lean_ctor_get(v_s_2819_, 3);
                v_stypeIdOf_2824_ = lean_ctor_get(v_s_2819_, 4);
                v_exprToSemiringId_2825_ = lean_ctor_get(v_s_2819_, 5);
                v_ncRings_2826_ = lean_ctor_get(v_s_2819_, 6);
                v_exprToNCRingId_2827_ = lean_ctor_get(v_s_2819_, 7);
                v_nctypeIdOf_2828_ = lean_ctor_get(v_s_2819_, 8);
                v_ncSemirings_2829_ = lean_ctor_get(v_s_2819_, 9);
                v_exprToNCSemiringId_2830_ = lean_ctor_get(v_s_2819_, 10);
                v_ncstypeIdOf_2831_ = lean_ctor_get(v_s_2819_, 11);
                v_steps_2832_ = lean_ctor_get(v_s_2819_, 12);
                v_reportedMaxDegreeIssue_2833_ = lean_ctor_get_uint8(
                    v_s_2819_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2841_ = (!lean_is_exclusive(v_s_2819_)) as u8;
                if v_isSharedCheck_2841_ == 0 {
                    v___x_2835_ = v_s_2819_;
                    v_isShared_2836_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_2832_);
                    lean_inc(v_ncstypeIdOf_2831_);
                    lean_inc(v_exprToNCSemiringId_2830_);
                    lean_inc(v_ncSemirings_2829_);
                    lean_inc(v_nctypeIdOf_2828_);
                    lean_inc(v_exprToNCRingId_2827_);
                    lean_inc(v_ncRings_2826_);
                    lean_inc(v_exprToSemiringId_2825_);
                    lean_inc(v_stypeIdOf_2824_);
                    lean_inc(v_semirings_2823_);
                    lean_inc(v_exprToRingId_2822_);
                    lean_inc(v_typeIdOf_2821_);
                    lean_inc(v_rings_2820_);
                    lean_dec(v_s_2819_);
                    v___x_2835_ = lean_box(0);
                    v_isShared_2836_ = v_isSharedCheck_2841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2837_ = lean_array_push(v_ncRings_2826_, v___x_2818_);
                if v_isShared_2836_ == 0 {
                    lean_ctor_set(v___x_2835_, 6, v___x_2837_);
                    v___x_2839_ = v___x_2835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_rings_2820_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_typeIdOf_2821_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_exprToRingId_2822_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_semirings_2823_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_stypeIdOf_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 5, v_exprToSemiringId_2825_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 6, v___x_2837_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_exprToNCRingId_2827_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 8, v_nctypeIdOf_2828_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 9, v_ncSemirings_2829_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 10, v_exprToNCSemiringId_2830_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 11, v_ncstypeIdOf_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 12, v_steps_2832_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2840_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_type_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
    mut v_a_2849_: *mut LeanObject,
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
    mut v_a_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v_options_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v_inheritedTraceOptions_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2876_: u8 = 0;
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2906_: u8 = 0;
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_unused_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v_a_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_a_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2954_: u8 = 0;
    let mut v_a_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_a_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2846_);
                v___x_2858_ = l_Lean_Meta_getDecLevel(
                    v_type_2846_,
                    v_a_2853_,
                    v_a_2854_,
                    v_a_2855_,
                    v_a_2856_,
                );
                if lean_obj_tag(v___x_2858_) == 0 {
                    v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
                    lean_inc_n(v_a_2859_, 2);
                    lean_dec_ref_known(v___x_2858_, 1);
                    v___x_2860_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___closed__0;
                    v___x_2861_ = lean_box(0);
                    v___x_2862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2862_, 0, v_a_2859_);
                    lean_ctor_set(v___x_2862_, 1, v___x_2861_);
                    lean_inc_ref(v___x_2862_);
                    v___x_2863_ = l_Lean_mkConst(v___x_2860_, v___x_2862_);
                    lean_inc_ref(v_type_2846_);
                    v___x_2864_ = l_Lean_Expr_app___override(v___x_2863_, v_type_2846_);
                    v___x_2865_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2864_,
                        v_a_2853_,
                        v_a_2854_,
                        v_a_2855_,
                        v_a_2856_,
                    );
                    if lean_obj_tag(v___x_2865_) == 0 {
                        v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
                        v_isSharedCheck_2968_ = (!lean_is_exclusive(v___x_2865_)) as u8;
                        if v_isSharedCheck_2968_ == 0 {
                            v___x_2868_ = v___x_2865_;
                            v_isShared_2869_ = v_isSharedCheck_2968_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2866_);
                            lean_dec(v___x_2865_);
                            v___x_2868_ = lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2968_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2862_, 2);
                        lean_dec(v_a_2859_);
                        lean_dec_ref(v_type_2846_);
                        v_a_2969_ = lean_ctor_get(v___x_2865_, 0);
                        v_isSharedCheck_2976_ = (!lean_is_exclusive(v___x_2865_)) as u8;
                        if v_isSharedCheck_2976_ == 0 {
                            v___x_2971_ = v___x_2865_;
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_2969_);
                            lean_dec(v___x_2865_);
                            v___x_2971_ = lean_box(0);
                            v_isShared_2972_ = v_isSharedCheck_2976_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2846_);
                    v_a_2977_ = lean_ctor_get(v___x_2858_, 0);
                    v_isSharedCheck_2984_ = (!lean_is_exclusive(v___x_2858_)) as u8;
                    if v_isSharedCheck_2984_ == 0 {
                        v___x_2979_ = v___x_2858_;
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2977_);
                        lean_dec(v___x_2858_);
                        v___x_2979_ = lean_box(0);
                        v_isShared_2980_ = v_isSharedCheck_2984_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2866_) == 1 {
                    lean_del_object(v___x_2868_);
                    v_options_2870_ = lean_ctor_get(v_a_2855_, 2);
                    v_val_2871_ = lean_ctor_get(v_a_2866_, 0);
                    v_isSharedCheck_2963_ = (!lean_is_exclusive(v_a_2866_)) as u8;
                    if v_isSharedCheck_2963_ == 0 {
                        v___x_2873_ = v_a_2866_;
                        v_isShared_2874_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2871_);
                        lean_dec(v_a_2866_);
                        v___x_2873_ = lean_box(0);
                        v_isShared_2874_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2866_);
                    lean_dec_ref_known(v___x_2862_, 2);
                    lean_dec(v_a_2859_);
                    lean_dec_ref(v_type_2846_);
                    v___x_2964_ = lean_box(0);
                    if v_isShared_2869_ == 0 {
                        lean_ctor_set(v___x_2868_, 0, v___x_2964_);
                        v___x_2966_ = v___x_2868_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                        v___x_2966_ = v_reuseFailAlloc_2967_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v_inheritedTraceOptions_2875_ = lean_ctor_get(v_a_2855_, 13);
                v_hasTrace_2876_ = lean_ctor_get_uint8(
                    v_options_2870_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_2877_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__11;
                v___x_2878_ = l_Lean_mkConst(v___x_2877_, v___x_2862_);
                lean_inc(v_val_2871_);
                lean_inc_ref(v_type_2846_);
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
                    v___x_2940_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__21);
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
                        if lean_obj_tag(v___x_2942_) == 0 {
                            lean_dec_ref_known(v___x_2942_, 1);
                            v___x_2943_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__29);
                            lean_inc_ref(v_type_2846_);
                            v___x_2944_ = l_Lean_MessageData_ofExpr(v_type_2846_);
                            v___x_2945_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2945_, 0, v___x_2943_);
                            lean_ctor_set(v___x_2945_, 1, v___x_2944_);
                            v___x_2946_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1___redArg(v___x_2939_, v___x_2945_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
                            if lean_obj_tag(v___x_2946_) == 0 {
                                lean_dec_ref_known(v___x_2946_, 1);
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
                                lean_dec_ref(v___x_2879_);
                                lean_del_object(v___x_2873_);
                                lean_dec(v_val_2871_);
                                lean_dec(v_a_2859_);
                                lean_dec_ref(v_type_2846_);
                                v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
                                v_isSharedCheck_2954_ = (!lean_is_exclusive(v___x_2946_)) as u8;
                                if v_isSharedCheck_2954_ == 0 {
                                    v___x_2949_ = v___x_2946_;
                                    v_isShared_2950_ = v_isSharedCheck_2954_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_2947_);
                                    lean_dec(v___x_2946_);
                                    v___x_2949_ = lean_box(0);
                                    v_isShared_2950_ = v_isSharedCheck_2954_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_2879_);
                            lean_del_object(v___x_2873_);
                            lean_dec(v_val_2871_);
                            lean_dec(v_a_2859_);
                            lean_dec_ref(v_type_2846_);
                            v_a_2955_ = lean_ctor_get(v___x_2942_, 0);
                            v_isSharedCheck_2962_ = (!lean_is_exclusive(v___x_2942_)) as u8;
                            if v_isSharedCheck_2962_ == 0 {
                                v___x_2957_ = v___x_2942_;
                                v_isShared_2958_ = v_isSharedCheck_2962_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_2955_);
                                lean_dec(v___x_2942_);
                                v___x_2957_ = lean_box(0);
                                v_isShared_2958_ = v_isSharedCheck_2962_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                lean_inc_ref(v___x_2879_);
                lean_inc_ref(v_type_2846_);
                lean_inc(v_a_2859_);
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
                if lean_obj_tag(v___x_2891_) == 0 {
                    v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
                    lean_inc(v_a_2892_);
                    lean_dec_ref_known(v___x_2891_, 1);
                    v___x_2893_ =
                        l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_2881_, v___y_2889_);
                    if lean_obj_tag(v___x_2893_) == 0 {
                        v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
                        lean_inc(v_a_2894_);
                        lean_dec_ref_known(v___x_2893_, 1);
                        v_ncRings_2895_ = lean_ctor_get(v_a_2894_, 6);
                        lean_inc_ref(v_ncRings_2895_);
                        lean_dec(v_a_2894_);
                        v___x_2896_ = lean_array_get_size(v_ncRings_2895_);
                        lean_dec_ref(v_ncRings_2895_);
                        v___x_2897_ = lean_box(0);
                        v___x_2898_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                        v___x_2899_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__17);
                        v___x_2900_ = lean_alloc_ctor(0, 17, (0) as u32);
                        lean_ctor_set(v___x_2900_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2900_, 1, v_type_2846_);
                        lean_ctor_set(v___x_2900_, 2, v_a_2859_);
                        lean_ctor_set(v___x_2900_, 3, v_val_2871_);
                        lean_ctor_set(v___x_2900_, 4, v___x_2879_);
                        lean_ctor_set(v___x_2900_, 5, v_a_2892_);
                        lean_ctor_set(v___x_2900_, 6, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 7, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 8, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 9, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 10, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 11, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 12, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 13, v___x_2897_);
                        lean_ctor_set(v___x_2900_, 14, v___x_2898_);
                        lean_ctor_set(v___x_2900_, 15, v___x_2899_);
                        lean_ctor_set(v___x_2900_, 16, v___x_2899_);
                        v___f_2901_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_2901_, 0, v___x_2900_);
                        v___x_2902_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_2903_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2902_, v___f_2901_, v___y_2881_);
                        if lean_obj_tag(v___x_2903_) == 0 {
                            v_isSharedCheck_2913_ = (!lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2913_ == 0 {
                                v_unused_2914_ = lean_ctor_get(v___x_2903_, 0);
                                lean_dec(v_unused_2914_);
                                v___x_2905_ = v___x_2903_;
                                v_isShared_2906_ = v_isSharedCheck_2913_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_2903_);
                                v___x_2905_ = lean_box(0);
                                v_isShared_2906_ = v_isSharedCheck_2913_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2873_);
                            v_a_2915_ = lean_ctor_get(v___x_2903_, 0);
                            v_isSharedCheck_2922_ = (!lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2922_ == 0 {
                                v___x_2917_ = v___x_2903_;
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2915_);
                                lean_dec(v___x_2903_);
                                v___x_2917_ = lean_box(0);
                                v_isShared_2918_ = v_isSharedCheck_2922_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2892_);
                        lean_dec_ref(v___x_2879_);
                        lean_del_object(v___x_2873_);
                        lean_dec(v_val_2871_);
                        lean_dec(v_a_2859_);
                        lean_dec_ref(v_type_2846_);
                        v_a_2923_ = lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2930_ = (!lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2930_ == 0 {
                            v___x_2925_ = v___x_2893_;
                            v_isShared_2926_ = v_isSharedCheck_2930_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2923_);
                            lean_dec(v___x_2893_);
                            v___x_2925_ = lean_box(0);
                            v_isShared_2926_ = v_isSharedCheck_2930_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2879_);
                    lean_del_object(v___x_2873_);
                    lean_dec(v_val_2871_);
                    lean_dec(v_a_2859_);
                    lean_dec_ref(v_type_2846_);
                    v_a_2931_ = lean_ctor_get(v___x_2891_, 0);
                    v_isSharedCheck_2938_ = (!lean_is_exclusive(v___x_2891_)) as u8;
                    if v_isSharedCheck_2938_ == 0 {
                        v___x_2933_ = v___x_2891_;
                        v_isShared_2934_ = v_isSharedCheck_2938_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2931_);
                        lean_dec(v___x_2891_);
                        v___x_2933_ = lean_box(0);
                        v_isShared_2934_ = v_isSharedCheck_2938_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2874_ == 0 {
                    lean_ctor_set(v___x_2873_, 0, v___x_2896_);
                    v___x_2908_ = v___x_2873_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2896_);
                    v___x_2908_ = v_reuseFailAlloc_2912_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2906_ == 0 {
                    lean_ctor_set(v___x_2905_, 0, v___x_2908_);
                    v___x_2910_ = v___x_2905_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
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
                    v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
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
                    v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
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
                    v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
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
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
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
                    v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
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
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
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
                    v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
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
    mut v_type_2985_: *mut LeanObject,
    mut v_a_2986_: *mut LeanObject,
    mut v_a_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2997_: *mut LeanObject = core::ptr::null_mut();
    v_res_2997_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
    lean_dec(v_a_2995_);
    lean_dec_ref(v_a_2994_);
    lean_dec(v_a_2993_);
    lean_dec_ref(v_a_2992_);
    lean_dec(v_a_2991_);
    lean_dec_ref(v_a_2990_);
    lean_dec(v_a_2989_);
    lean_dec_ref(v_a_2988_);
    lean_dec(v_a_2987_);
    lean_dec(v_a_2986_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(
    mut v_type_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_s_3000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3014_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3001_ = lean_ctor_get(v_s_3000_, 0);
                v_typeIdOf_3002_ = lean_ctor_get(v_s_3000_, 1);
                v_exprToRingId_3003_ = lean_ctor_get(v_s_3000_, 2);
                v_semirings_3004_ = lean_ctor_get(v_s_3000_, 3);
                v_stypeIdOf_3005_ = lean_ctor_get(v_s_3000_, 4);
                v_exprToSemiringId_3006_ = lean_ctor_get(v_s_3000_, 5);
                v_ncRings_3007_ = lean_ctor_get(v_s_3000_, 6);
                v_exprToNCRingId_3008_ = lean_ctor_get(v_s_3000_, 7);
                v_nctypeIdOf_3009_ = lean_ctor_get(v_s_3000_, 8);
                v_ncSemirings_3010_ = lean_ctor_get(v_s_3000_, 9);
                v_exprToNCSemiringId_3011_ = lean_ctor_get(v_s_3000_, 10);
                v_ncstypeIdOf_3012_ = lean_ctor_get(v_s_3000_, 11);
                v_steps_3013_ = lean_ctor_get(v_s_3000_, 12);
                v_reportedMaxDegreeIssue_3014_ = lean_ctor_get_uint8(
                    v_s_3000_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3022_ = (!lean_is_exclusive(v_s_3000_)) as u8;
                if v_isSharedCheck_3022_ == 0 {
                    v___x_3016_ = v_s_3000_;
                    v_isShared_3017_ = v_isSharedCheck_3022_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3013_);
                    lean_inc(v_ncstypeIdOf_3012_);
                    lean_inc(v_exprToNCSemiringId_3011_);
                    lean_inc(v_ncSemirings_3010_);
                    lean_inc(v_nctypeIdOf_3009_);
                    lean_inc(v_exprToNCRingId_3008_);
                    lean_inc(v_ncRings_3007_);
                    lean_inc(v_exprToSemiringId_3006_);
                    lean_inc(v_stypeIdOf_3005_);
                    lean_inc(v_semirings_3004_);
                    lean_inc(v_exprToRingId_3003_);
                    lean_inc(v_typeIdOf_3002_);
                    lean_inc(v_rings_3001_);
                    lean_dec(v_s_3000_);
                    v___x_3016_ = lean_box(0);
                    v_isShared_3017_ = v_isSharedCheck_3022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3018_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_3009_, v_type_2998_, v_a_2999_);
                if v_isShared_3017_ == 0 {
                    lean_ctor_set(v___x_3016_, 8, v___x_3018_);
                    v___x_3020_ = v___x_3016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_rings_3001_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_typeIdOf_3002_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_exprToRingId_3003_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_semirings_3004_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_stypeIdOf_3005_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 5, v_exprToSemiringId_3006_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 6, v_ncRings_3007_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 7, v_exprToNCRingId_3008_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 8, v___x_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 9, v_ncSemirings_3010_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 10, v_exprToNCSemiringId_3011_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 11, v_ncstypeIdOf_3012_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 12, v_steps_3013_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3021_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_type_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
    mut v_a_3029_: *mut LeanObject,
    mut v_a_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
    mut v_a_3032_: *mut LeanObject,
    mut v_a_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v_nctypeIdOf_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_unused_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_a_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3035_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3024_, v_a_3032_);
                if lean_obj_tag(v___x_3035_) == 0 {
                    v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
                    v_isSharedCheck_3067_ = (!lean_is_exclusive(v___x_3035_)) as u8;
                    if v_isSharedCheck_3067_ == 0 {
                        v___x_3038_ = v___x_3035_;
                        v_isShared_3039_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3036_);
                        lean_dec(v___x_3035_);
                        v___x_3038_ = lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3023_);
                    v_a_3068_ = lean_ctor_get(v___x_3035_, 0);
                    v_isSharedCheck_3075_ = (!lean_is_exclusive(v___x_3035_)) as u8;
                    if v_isSharedCheck_3075_ == 0 {
                        v___x_3070_ = v___x_3035_;
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3068_);
                        lean_dec(v___x_3035_);
                        v___x_3070_ = lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_nctypeIdOf_3040_ = lean_ctor_get(v_a_3036_, 8);
                lean_inc_ref(v_nctypeIdOf_3040_);
                lean_dec(v_a_3036_);
                v___x_3041_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_3040_, v_type_3023_);
                lean_dec_ref(v_nctypeIdOf_3040_);
                if lean_obj_tag(v___x_3041_) == 1 {
                    lean_dec_ref(v_type_3023_);
                    v_val_3042_ = lean_ctor_get(v___x_3041_, 0);
                    lean_inc(v_val_3042_);
                    lean_dec_ref_known(v___x_3041_, 1);
                    if v_isShared_3039_ == 0 {
                        lean_ctor_set(v___x_3038_, 0, v_val_3042_);
                        v___x_3044_ = v___x_3038_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_val_3042_);
                        v___x_3044_ = v_reuseFailAlloc_3045_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3041_);
                    lean_del_object(v___x_3038_);
                    lean_inc_ref(v_type_3023_);
                    v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
                    if lean_obj_tag(v___x_3046_) == 0 {
                        v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
                        lean_inc_n(v_a_3047_, 2);
                        lean_dec_ref_known(v___x_3046_, 1);
                        v___f_3048_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3048_, 0, v_type_3023_);
                        lean_closure_set(v___f_3048_, 1, v_a_3047_);
                        v___x_3049_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3050_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3049_, v___f_3048_, v_a_3024_);
                        if lean_obj_tag(v___x_3050_) == 0 {
                            v_isSharedCheck_3057_ = (!lean_is_exclusive(v___x_3050_)) as u8;
                            if v_isSharedCheck_3057_ == 0 {
                                v_unused_3058_ = lean_ctor_get(v___x_3050_, 0);
                                lean_dec(v_unused_3058_);
                                v___x_3052_ = v___x_3050_;
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3050_);
                                v___x_3052_ = lean_box(0);
                                v_isShared_3053_ = v_isSharedCheck_3057_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3047_);
                            v_a_3059_ = lean_ctor_get(v___x_3050_, 0);
                            v_isSharedCheck_3066_ = (!lean_is_exclusive(v___x_3050_)) as u8;
                            if v_isSharedCheck_3066_ == 0 {
                                v___x_3061_ = v___x_3050_;
                                v_isShared_3062_ = v_isSharedCheck_3066_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3059_);
                                lean_dec(v___x_3050_);
                                v___x_3061_ = lean_box(0);
                                v_isShared_3062_ = v_isSharedCheck_3066_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_3023_);
                        return v___x_3046_;
                    }
                }
            }
            2 => {
                return v___x_3044_;
            }
            3 => {
                if v_isShared_3053_ == 0 {
                    lean_ctor_set(v___x_3052_, 0, v_a_3047_);
                    v___x_3055_ = v___x_3052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3047_);
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
                    v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
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
                    v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
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
    mut v_type_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
    mut v_a_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3088_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3086_);
    lean_dec_ref(v_a_3085_);
    lean_dec(v_a_3084_);
    lean_dec_ref(v_a_3083_);
    lean_dec(v_a_3082_);
    lean_dec_ref(v_a_3081_);
    lean_dec(v_a_3080_);
    lean_dec_ref(v_a_3079_);
    lean_dec(v_a_3078_);
    lean_dec(v_a_3077_);
    return v_res_3088_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(
    mut v_semiringId_3089_: *mut LeanObject,
    mut v_s_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_3104_: u8 = 0;
    let mut v_invSet_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_3108_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_unused_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_3091_ = lean_ctor_get(v_s_3090_, 0);
                v_invFn_x3f_3092_ = lean_ctor_get(v_s_3090_, 1);
                v_commSemiringInst_3093_ = lean_ctor_get(v_s_3090_, 3);
                v_commRingInst_3094_ = lean_ctor_get(v_s_3090_, 4);
                v_noZeroDivInst_x3f_3095_ = lean_ctor_get(v_s_3090_, 5);
                v_fieldInst_x3f_3096_ = lean_ctor_get(v_s_3090_, 6);
                v_powIdentityInst_x3f_3097_ = lean_ctor_get(v_s_3090_, 7);
                v_denoteEntries_3098_ = lean_ctor_get(v_s_3090_, 8);
                v_nextId_3099_ = lean_ctor_get(v_s_3090_, 9);
                v_steps_3100_ = lean_ctor_get(v_s_3090_, 10);
                v_queue_3101_ = lean_ctor_get(v_s_3090_, 11);
                v_basis_3102_ = lean_ctor_get(v_s_3090_, 12);
                v_diseqs_3103_ = lean_ctor_get(v_s_3090_, 13);
                v_recheck_3104_ = lean_ctor_get_uint8(
                    v_s_3090_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_3105_ = lean_ctor_get(v_s_3090_, 14);
                v_powIdentityVarCount_3106_ = lean_ctor_get(v_s_3090_, 15);
                v_numEq0_x3f_3107_ = lean_ctor_get(v_s_3090_, 16);
                v_numEq0Updated_3108_ = lean_ctor_get_uint8(
                    v_s_3090_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_3116_ = (!lean_is_exclusive(v_s_3090_)) as u8;
                if v_isSharedCheck_3116_ == 0 {
                    v_unused_3117_ = lean_ctor_get(v_s_3090_, 2);
                    lean_dec(v_unused_3117_);
                    v___x_3110_ = v_s_3090_;
                    v_isShared_3111_ = v_isSharedCheck_3116_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_3107_);
                    lean_inc(v_powIdentityVarCount_3106_);
                    lean_inc(v_invSet_3105_);
                    lean_inc(v_diseqs_3103_);
                    lean_inc(v_basis_3102_);
                    lean_inc(v_queue_3101_);
                    lean_inc(v_steps_3100_);
                    lean_inc(v_nextId_3099_);
                    lean_inc(v_denoteEntries_3098_);
                    lean_inc(v_powIdentityInst_x3f_3097_);
                    lean_inc(v_fieldInst_x3f_3096_);
                    lean_inc(v_noZeroDivInst_x3f_3095_);
                    lean_inc(v_commRingInst_3094_);
                    lean_inc(v_commSemiringInst_3093_);
                    lean_inc(v_invFn_x3f_3092_);
                    lean_inc(v_toRing_3091_);
                    lean_dec(v_s_3090_);
                    v___x_3110_ = lean_box(0);
                    v_isShared_3111_ = v_isSharedCheck_3116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3112_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3112_, 0, v_semiringId_3089_);
                if v_isShared_3111_ == 0 {
                    lean_ctor_set(v___x_3110_, 2, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_toRing_3091_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_invFn_x3f_3092_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 2, v___x_3112_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_commSemiringInst_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_commRingInst_3094_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 5, v_noZeroDivInst_x3f_3095_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 6, v_fieldInst_x3f_3096_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 7, v_powIdentityInst_x3f_3097_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 8, v_denoteEntries_3098_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 9, v_nextId_3099_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 10, v_steps_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 11, v_queue_3101_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 12, v_basis_3102_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 13, v_diseqs_3103_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 14, v_invSet_3105_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 15, v_powIdentityVarCount_3106_);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 16, v_numEq0_x3f_3107_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3115_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_3104_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3115_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v_ringId_3118_: *mut LeanObject,
    mut v_semiringId_3119_: *mut LeanObject,
    mut v_a_3120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    v___f_3122_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_3122_, 0, v_semiringId_3119_);
    v___x_3123_ = 0;
    v___x_3124_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_3124_, 0, v_ringId_3118_);
    lean_ctor_set_uint8(
        v___x_3124_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3123_,
    );
    v___x_3125_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v___f_3122_,
        v___x_3124_,
        v_a_3120_,
    );
    lean_dec_ref_known(v___x_3124_, 1);
    return v___x_3125_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(
    mut v_ringId_3126_: *mut LeanObject,
    mut v_semiringId_3127_: *mut LeanObject,
    mut v_a_3128_: *mut LeanObject,
    mut v_a_3129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3130_: *mut LeanObject = core::ptr::null_mut();
    v_res_3130_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_3126_, v_semiringId_3127_, v_a_3128_);
    lean_dec(v_a_3128_);
    return v_res_3130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(
    mut v_ringId_3131_: *mut LeanObject,
    mut v_semiringId_3132_: *mut LeanObject,
    mut v_a_3133_: *mut LeanObject,
    mut v_a_3134_: *mut LeanObject,
    mut v_a_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    v___x_3144_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_3131_, v_semiringId_3132_, v_a_3133_);
    return v___x_3144_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(
    mut v_ringId_3145_: *mut LeanObject,
    mut v_semiringId_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3158_: *mut LeanObject = core::ptr::null_mut();
    v_res_3158_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_3145_, v_semiringId_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
    lean_dec(v_a_3156_);
    lean_dec_ref(v_a_3155_);
    lean_dec(v_a_3154_);
    lean_dec_ref(v_a_3153_);
    lean_dec(v_a_3152_);
    lean_dec_ref(v_a_3151_);
    lean_dec(v_a_3150_);
    lean_dec_ref(v_a_3149_);
    lean_dec(v_a_3148_);
    lean_dec(v_a_3147_);
    return v_res_3158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(
    mut v___x_3159_: *mut LeanObject,
    mut v_s_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3174_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3161_ = lean_ctor_get(v_s_3160_, 0);
                v_typeIdOf_3162_ = lean_ctor_get(v_s_3160_, 1);
                v_exprToRingId_3163_ = lean_ctor_get(v_s_3160_, 2);
                v_semirings_3164_ = lean_ctor_get(v_s_3160_, 3);
                v_stypeIdOf_3165_ = lean_ctor_get(v_s_3160_, 4);
                v_exprToSemiringId_3166_ = lean_ctor_get(v_s_3160_, 5);
                v_ncRings_3167_ = lean_ctor_get(v_s_3160_, 6);
                v_exprToNCRingId_3168_ = lean_ctor_get(v_s_3160_, 7);
                v_nctypeIdOf_3169_ = lean_ctor_get(v_s_3160_, 8);
                v_ncSemirings_3170_ = lean_ctor_get(v_s_3160_, 9);
                v_exprToNCSemiringId_3171_ = lean_ctor_get(v_s_3160_, 10);
                v_ncstypeIdOf_3172_ = lean_ctor_get(v_s_3160_, 11);
                v_steps_3173_ = lean_ctor_get(v_s_3160_, 12);
                v_reportedMaxDegreeIssue_3174_ = lean_ctor_get_uint8(
                    v_s_3160_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3182_ = (!lean_is_exclusive(v_s_3160_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3176_ = v_s_3160_;
                    v_isShared_3177_ = v_isSharedCheck_3182_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3173_);
                    lean_inc(v_ncstypeIdOf_3172_);
                    lean_inc(v_exprToNCSemiringId_3171_);
                    lean_inc(v_ncSemirings_3170_);
                    lean_inc(v_nctypeIdOf_3169_);
                    lean_inc(v_exprToNCRingId_3168_);
                    lean_inc(v_ncRings_3167_);
                    lean_inc(v_exprToSemiringId_3166_);
                    lean_inc(v_stypeIdOf_3165_);
                    lean_inc(v_semirings_3164_);
                    lean_inc(v_exprToRingId_3163_);
                    lean_inc(v_typeIdOf_3162_);
                    lean_inc(v_rings_3161_);
                    lean_dec(v_s_3160_);
                    v___x_3176_ = lean_box(0);
                    v_isShared_3177_ = v_isSharedCheck_3182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3178_ = lean_array_push(v_semirings_3164_, v___x_3159_);
                if v_isShared_3177_ == 0 {
                    lean_ctor_set(v___x_3176_, 3, v___x_3178_);
                    v___x_3180_ = v___x_3176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_rings_3161_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_typeIdOf_3162_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_exprToRingId_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 3, v___x_3178_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_stypeIdOf_3165_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 5, v_exprToSemiringId_3166_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_ncRings_3167_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_exprToNCRingId_3168_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 8, v_nctypeIdOf_3169_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 9, v_ncSemirings_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 10, v_exprToNCSemiringId_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 11, v_ncstypeIdOf_3172_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 12, v_steps_3173_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3181_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_msg_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
    mut v___y_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3189_ = lean_ctor_get(v___y_3186_, 5);
                v___x_3190_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f_spec__1_spec__1(v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
                v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
                v_isSharedCheck_3199_ = (!lean_is_exclusive(v___x_3190_)) as u8;
                if v_isSharedCheck_3199_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    v_isShared_3194_ = v_isSharedCheck_3199_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3191_);
                    lean_dec(v___x_3190_);
                    v___x_3193_ = lean_box(0);
                    v_isShared_3194_ = v_isSharedCheck_3199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3189_);
                v___x_3195_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3195_, 0, v_ref_3189_);
                lean_ctor_set(v___x_3195_, 1, v_a_3191_);
                if v_isShared_3194_ == 0 {
                    lean_ctor_set_tag(v___x_3193_, 1);
                    lean_ctor_set(v___x_3193_, 0, v___x_3195_);
                    v___x_3197_ = v___x_3193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
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
    mut v_msg_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3206_: *mut LeanObject = core::ptr::null_mut();
    v_res_3206_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
    lean_dec(v___y_3204_);
    lean_dec_ref(v___y_3203_);
    lean_dec(v___y_3202_);
    lean_dec_ref(v___y_3201_);
    return v_res_3206_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6()
-> *mut LeanObject {
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    v___x_3225_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3225_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7()
-> *mut LeanObject {
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    v___x_3226_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__6);
    v___x_3227_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3227_, 0, v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9()
-> *mut LeanObject {
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    v___x_3229_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__8;
    v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
    return v___x_3230_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(
    mut v_type_3231_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v_val_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut v_unused_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3303_: u8 = 0;
    let mut v_a_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3311_: u8 = 0;
    let mut v_a_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3328_: u8 = 0;
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v_a_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v_a_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3349_: u8 = 0;
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_a_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3357_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_3231_);
                v___x_3243_ = l_Lean_Meta_getDecLevel(
                    v_type_3231_,
                    v_a_3238_,
                    v_a_3239_,
                    v_a_3240_,
                    v_a_3241_,
                );
                if lean_obj_tag(v___x_3243_) == 0 {
                    v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
                    lean_inc_n(v_a_3244_, 2);
                    lean_dec_ref_known(v___x_3243_, 1);
                    v___x_3245_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1;
                    v___x_3246_ = lean_box(0);
                    v___x_3247_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3247_, 0, v_a_3244_);
                    lean_ctor_set(v___x_3247_, 1, v___x_3246_);
                    lean_inc_ref(v___x_3247_);
                    v___x_3248_ = l_Lean_mkConst(v___x_3245_, v___x_3247_);
                    lean_inc_ref(v_type_3231_);
                    v___x_3249_ = l_Lean_Expr_app___override(v___x_3248_, v_type_3231_);
                    v___x_3250_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3249_,
                        v_a_3238_,
                        v_a_3239_,
                        v_a_3240_,
                        v_a_3241_,
                    );
                    if lean_obj_tag(v___x_3250_) == 0 {
                        v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
                        v_isSharedCheck_3345_ = (!lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3345_ == 0 {
                            v___x_3253_ = v___x_3250_;
                            v_isShared_3254_ = v_isSharedCheck_3345_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3251_);
                            lean_dec(v___x_3250_);
                            v___x_3253_ = lean_box(0);
                            v_isShared_3254_ = v_isSharedCheck_3345_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_3247_, 2);
                        lean_dec(v_a_3244_);
                        lean_dec_ref(v_type_3231_);
                        v_a_3346_ = lean_ctor_get(v___x_3250_, 0);
                        v_isSharedCheck_3353_ = (!lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3353_ == 0 {
                            v___x_3348_ = v___x_3250_;
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3346_);
                            lean_dec(v___x_3250_);
                            v___x_3348_ = lean_box(0);
                            v_isShared_3349_ = v_isSharedCheck_3353_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3231_);
                    v_a_3354_ = lean_ctor_get(v___x_3243_, 0);
                    v_isSharedCheck_3361_ = (!lean_is_exclusive(v___x_3243_)) as u8;
                    if v_isSharedCheck_3361_ == 0 {
                        v___x_3356_ = v___x_3243_;
                        v_isShared_3357_ = v_isSharedCheck_3361_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3354_);
                        lean_dec(v___x_3243_);
                        v___x_3356_ = lean_box(0);
                        v_isShared_3357_ = v_isSharedCheck_3361_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3251_) == 1 {
                    lean_del_object(v___x_3253_);
                    v_val_3255_ = lean_ctor_get(v_a_3251_, 0);
                    lean_inc_n(v_val_3255_, 2);
                    lean_dec_ref_known(v_a_3251_, 1);
                    v___x_3256_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2;
                    lean_inc_ref(v___x_3247_);
                    v___x_3257_ = l_Lean_mkConst(v___x_3256_, v___x_3247_);
                    lean_inc_ref_n(v_type_3231_, 2);
                    v___x_3258_ = l_Lean_mkAppB(v___x_3257_, v_type_3231_, v_val_3255_);
                    v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__5;
                    v___x_3260_ = l_Lean_mkConst(v___x_3259_, v___x_3247_);
                    lean_inc_ref(v___x_3258_);
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
                    if lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
                        lean_inc(v_a_3263_);
                        lean_dec_ref_known(v___x_3262_, 1);
                        v___x_3264_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3263_, v_a_3237_);
                        if lean_obj_tag(v___x_3264_) == 0 {
                            v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
                            lean_inc_n(v_a_3265_, 2);
                            lean_dec_ref_known(v___x_3264_, 1);
                            v___x_3266_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                                v_a_3265_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_,
                                v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_,
                            );
                            if lean_obj_tag(v___x_3266_) == 0 {
                                v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                                lean_inc(v_a_3267_);
                                lean_dec_ref_known(v___x_3266_, 1);
                                if lean_obj_tag(v_a_3267_) == 1 {
                                    lean_dec(v_a_3265_);
                                    v_val_3268_ = lean_ctor_get(v_a_3267_, 0);
                                    v_isSharedCheck_3320_ = (!lean_is_exclusive(v_a_3267_)) as u8;
                                    if v_isSharedCheck_3320_ == 0 {
                                        v___x_3270_ = v_a_3267_;
                                        v_isShared_3271_ = v_isSharedCheck_3320_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_val_3268_);
                                        lean_dec(v_a_3267_);
                                        v___x_3270_ = lean_box(0);
                                        v_isShared_3271_ = v_isSharedCheck_3320_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3267_);
                                    lean_dec_ref(v___x_3258_);
                                    lean_dec(v_val_3255_);
                                    lean_dec(v_a_3244_);
                                    lean_dec_ref(v_type_3231_);
                                    v___x_3321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__9);
                                    v___x_3322_ = l_Lean_indentExpr(v_a_3265_);
                                    v___x_3323_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3323_, 0, v___x_3321_);
                                    lean_ctor_set(v___x_3323_, 1, v___x_3322_);
                                    v___x_3324_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_3323_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
                                    return v___x_3324_;
                                }
                            } else {
                                lean_dec(v_a_3265_);
                                lean_dec_ref(v___x_3258_);
                                lean_dec(v_val_3255_);
                                lean_dec(v_a_3244_);
                                lean_dec_ref(v_type_3231_);
                                return v___x_3266_;
                            }
                        } else {
                            lean_dec_ref(v___x_3258_);
                            lean_dec(v_val_3255_);
                            lean_dec(v_a_3244_);
                            lean_dec_ref(v_type_3231_);
                            v_a_3325_ = lean_ctor_get(v___x_3264_, 0);
                            v_isSharedCheck_3332_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                            if v_isSharedCheck_3332_ == 0 {
                                v___x_3327_ = v___x_3264_;
                                v_isShared_3328_ = v_isSharedCheck_3332_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3325_);
                                lean_dec(v___x_3264_);
                                v___x_3327_ = lean_box(0);
                                v_isShared_3328_ = v_isSharedCheck_3332_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3258_);
                        lean_dec(v_val_3255_);
                        lean_dec(v_a_3244_);
                        lean_dec_ref(v_type_3231_);
                        v_a_3333_ = lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3340_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3340_ == 0 {
                            v___x_3335_ = v___x_3262_;
                            v_isShared_3336_ = v_isSharedCheck_3340_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_3333_);
                            lean_dec(v___x_3262_);
                            v___x_3335_ = lean_box(0);
                            v_isShared_3336_ = v_isSharedCheck_3340_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3251_);
                    lean_dec_ref_known(v___x_3247_, 2);
                    lean_dec(v_a_3244_);
                    lean_dec_ref(v_type_3231_);
                    v___x_3341_ = lean_box(0);
                    if v_isShared_3254_ == 0 {
                        lean_ctor_set(v___x_3253_, 0, v___x_3341_);
                        v___x_3343_ = v___x_3253_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
                        v___x_3343_ = v_reuseFailAlloc_3344_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3272_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3232_, v_a_3240_);
                if lean_obj_tag(v___x_3272_) == 0 {
                    v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
                    lean_inc(v_a_3273_);
                    lean_dec_ref_known(v___x_3272_, 1);
                    v_semirings_3274_ = lean_ctor_get(v_a_3273_, 3);
                    lean_inc_ref(v_semirings_3274_);
                    lean_dec(v_a_3273_);
                    v___x_3275_ = lean_array_get_size(v_semirings_3274_);
                    lean_dec_ref(v_semirings_3274_);
                    v___x_3276_ = lean_box(0);
                    v___x_3277_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
                    v___x_3278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_3279_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v___x_3279_, 0, v___x_3275_);
                    lean_ctor_set(v___x_3279_, 1, v_type_3231_);
                    lean_ctor_set(v___x_3279_, 2, v_a_3244_);
                    lean_ctor_set(v___x_3279_, 3, v___x_3258_);
                    lean_ctor_set(v___x_3279_, 4, v___x_3276_);
                    lean_ctor_set(v___x_3279_, 5, v___x_3276_);
                    lean_ctor_set(v___x_3279_, 6, v___x_3276_);
                    lean_ctor_set(v___x_3279_, 7, v___x_3276_);
                    lean_ctor_set(v___x_3279_, 8, v___x_3277_);
                    lean_ctor_set(v___x_3279_, 9, v___x_3278_);
                    lean_ctor_set(v___x_3279_, 10, v___x_3277_);
                    lean_inc(v_val_3268_);
                    v___x_3280_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3280_, 0, v___x_3279_);
                    lean_ctor_set(v___x_3280_, 1, v_val_3268_);
                    lean_ctor_set(v___x_3280_, 2, v_val_3255_);
                    lean_ctor_set(v___x_3280_, 3, v___x_3276_);
                    lean_ctor_set(v___x_3280_, 4, v___x_3276_);
                    v___f_3281_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_3281_, 0, v___x_3280_);
                    v___x_3282_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3283_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3282_, v___f_3281_, v_a_3232_);
                    if lean_obj_tag(v___x_3283_) == 0 {
                        lean_dec_ref_known(v___x_3283_, 1);
                        v___x_3284_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_3268_, v___x_3275_, v_a_3232_);
                        if lean_obj_tag(v___x_3284_) == 0 {
                            v_isSharedCheck_3294_ = (!lean_is_exclusive(v___x_3284_)) as u8;
                            if v_isSharedCheck_3294_ == 0 {
                                v_unused_3295_ = lean_ctor_get(v___x_3284_, 0);
                                lean_dec(v_unused_3295_);
                                v___x_3286_ = v___x_3284_;
                                v_isShared_3287_ = v_isSharedCheck_3294_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3284_);
                                v___x_3286_ = lean_box(0);
                                v_isShared_3287_ = v_isSharedCheck_3294_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3270_);
                            v_a_3296_ = lean_ctor_get(v___x_3284_, 0);
                            v_isSharedCheck_3303_ = (!lean_is_exclusive(v___x_3284_)) as u8;
                            if v_isSharedCheck_3303_ == 0 {
                                v___x_3298_ = v___x_3284_;
                                v_isShared_3299_ = v_isSharedCheck_3303_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3296_);
                                lean_dec(v___x_3284_);
                                v___x_3298_ = lean_box(0);
                                v_isShared_3299_ = v_isSharedCheck_3303_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3270_);
                        lean_dec(v_val_3268_);
                        v_a_3304_ = lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3311_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3311_ == 0 {
                            v___x_3306_ = v___x_3283_;
                            v_isShared_3307_ = v_isSharedCheck_3311_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3304_);
                            lean_dec(v___x_3283_);
                            v___x_3306_ = lean_box(0);
                            v_isShared_3307_ = v_isSharedCheck_3311_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3270_);
                    lean_dec(v_val_3268_);
                    lean_dec_ref(v___x_3258_);
                    lean_dec(v_val_3255_);
                    lean_dec(v_a_3244_);
                    lean_dec_ref(v_type_3231_);
                    v_a_3312_ = lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3314_ = v___x_3272_;
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3312_);
                        lean_dec(v___x_3272_);
                        v___x_3314_ = lean_box(0);
                        v_isShared_3315_ = v_isSharedCheck_3319_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3271_ == 0 {
                    lean_ctor_set(v___x_3270_, 0, v___x_3275_);
                    v___x_3289_ = v___x_3270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3275_);
                    v___x_3289_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3287_ == 0 {
                    lean_ctor_set(v___x_3286_, 0, v___x_3289_);
                    v___x_3291_ = v___x_3286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
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
                    v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
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
                    v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
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
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
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
                    v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
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
                    v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
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
                    v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
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
                    v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
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
    mut v_type_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
    mut v_a_3365_: *mut LeanObject,
    mut v_a_3366_: *mut LeanObject,
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
    mut v_a_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
    mut v_a_3372_: *mut LeanObject,
    mut v_a_3373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3374_: *mut LeanObject = core::ptr::null_mut();
    v_res_3374_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
    lean_dec(v_a_3372_);
    lean_dec_ref(v_a_3371_);
    lean_dec(v_a_3370_);
    lean_dec_ref(v_a_3369_);
    lean_dec(v_a_3368_);
    lean_dec_ref(v_a_3367_);
    lean_dec(v_a_3366_);
    lean_dec_ref(v_a_3365_);
    lean_dec(v_a_3364_);
    lean_dec(v_a_3363_);
    return v_res_3374_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(
    mut v_00_u03b1_3375_: *mut LeanObject,
    mut v_msg_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    v___x_3388_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_3376_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
    return v___x_3388_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(
    mut v_00_u03b1_3389_: *mut LeanObject,
    mut v_msg_3390_: *mut LeanObject,
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
    mut v___y_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_3389_, v_msg_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
    lean_dec(v___y_3400_);
    lean_dec_ref(v___y_3399_);
    lean_dec(v___y_3398_);
    lean_dec_ref(v___y_3397_);
    lean_dec(v___y_3396_);
    lean_dec_ref(v___y_3395_);
    lean_dec(v___y_3394_);
    lean_dec_ref(v___y_3393_);
    lean_dec(v___y_3392_);
    lean_dec(v___y_3391_);
    return v_res_3402_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(
    mut v_type_3403_: *mut LeanObject,
    mut v_a_3404_: *mut LeanObject,
    mut v_s_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3419_: u8 = 0;
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3406_ = lean_ctor_get(v_s_3405_, 0);
                v_typeIdOf_3407_ = lean_ctor_get(v_s_3405_, 1);
                v_exprToRingId_3408_ = lean_ctor_get(v_s_3405_, 2);
                v_semirings_3409_ = lean_ctor_get(v_s_3405_, 3);
                v_stypeIdOf_3410_ = lean_ctor_get(v_s_3405_, 4);
                v_exprToSemiringId_3411_ = lean_ctor_get(v_s_3405_, 5);
                v_ncRings_3412_ = lean_ctor_get(v_s_3405_, 6);
                v_exprToNCRingId_3413_ = lean_ctor_get(v_s_3405_, 7);
                v_nctypeIdOf_3414_ = lean_ctor_get(v_s_3405_, 8);
                v_ncSemirings_3415_ = lean_ctor_get(v_s_3405_, 9);
                v_exprToNCSemiringId_3416_ = lean_ctor_get(v_s_3405_, 10);
                v_ncstypeIdOf_3417_ = lean_ctor_get(v_s_3405_, 11);
                v_steps_3418_ = lean_ctor_get(v_s_3405_, 12);
                v_reportedMaxDegreeIssue_3419_ = lean_ctor_get_uint8(
                    v_s_3405_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3427_ = (!lean_is_exclusive(v_s_3405_)) as u8;
                if v_isSharedCheck_3427_ == 0 {
                    v___x_3421_ = v_s_3405_;
                    v_isShared_3422_ = v_isSharedCheck_3427_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3418_);
                    lean_inc(v_ncstypeIdOf_3417_);
                    lean_inc(v_exprToNCSemiringId_3416_);
                    lean_inc(v_ncSemirings_3415_);
                    lean_inc(v_nctypeIdOf_3414_);
                    lean_inc(v_exprToNCRingId_3413_);
                    lean_inc(v_ncRings_3412_);
                    lean_inc(v_exprToSemiringId_3411_);
                    lean_inc(v_stypeIdOf_3410_);
                    lean_inc(v_semirings_3409_);
                    lean_inc(v_exprToRingId_3408_);
                    lean_inc(v_typeIdOf_3407_);
                    lean_inc(v_rings_3406_);
                    lean_dec(v_s_3405_);
                    v___x_3421_ = lean_box(0);
                    v_isShared_3422_ = v_isSharedCheck_3427_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3423_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_3410_, v_type_3403_, v_a_3404_);
                if v_isShared_3422_ == 0 {
                    lean_ctor_set(v___x_3421_, 4, v___x_3423_);
                    v___x_3425_ = v___x_3421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_rings_3406_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_typeIdOf_3407_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_exprToRingId_3408_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_semirings_3409_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 4, v___x_3423_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_exprToSemiringId_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_ncRings_3412_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_exprToNCRingId_3413_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_nctypeIdOf_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 9, v_ncSemirings_3415_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 10, v_exprToNCSemiringId_3416_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 11, v_ncstypeIdOf_3417_);
                    lean_ctor_set(v_reuseFailAlloc_3426_, 12, v_steps_3418_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3426_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_type_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
    mut v_a_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
    mut v_a_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v_stypeIdOf_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_isSharedCheck_3472_: u8 = 0;
    let mut v_a_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3440_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3429_, v_a_3437_);
                if lean_obj_tag(v___x_3440_) == 0 {
                    v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
                    v_isSharedCheck_3472_ = (!lean_is_exclusive(v___x_3440_)) as u8;
                    if v_isSharedCheck_3472_ == 0 {
                        v___x_3443_ = v___x_3440_;
                        v_isShared_3444_ = v_isSharedCheck_3472_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3441_);
                        lean_dec(v___x_3440_);
                        v___x_3443_ = lean_box(0);
                        v_isShared_3444_ = v_isSharedCheck_3472_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3428_);
                    v_a_3473_ = lean_ctor_get(v___x_3440_, 0);
                    v_isSharedCheck_3480_ = (!lean_is_exclusive(v___x_3440_)) as u8;
                    if v_isSharedCheck_3480_ == 0 {
                        v___x_3475_ = v___x_3440_;
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3473_);
                        lean_dec(v___x_3440_);
                        v___x_3475_ = lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3480_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_stypeIdOf_3445_ = lean_ctor_get(v_a_3441_, 4);
                lean_inc_ref(v_stypeIdOf_3445_);
                lean_dec(v_a_3441_);
                v___x_3446_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_3445_, v_type_3428_);
                lean_dec_ref(v_stypeIdOf_3445_);
                if lean_obj_tag(v___x_3446_) == 1 {
                    lean_dec_ref(v_type_3428_);
                    v_val_3447_ = lean_ctor_get(v___x_3446_, 0);
                    lean_inc(v_val_3447_);
                    lean_dec_ref_known(v___x_3446_, 1);
                    if v_isShared_3444_ == 0 {
                        lean_ctor_set(v___x_3443_, 0, v_val_3447_);
                        v___x_3449_ = v___x_3443_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_val_3447_);
                        v___x_3449_ = v_reuseFailAlloc_3450_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3446_);
                    lean_del_object(v___x_3443_);
                    lean_inc_ref(v_type_3428_);
                    v___x_3451_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
                    if lean_obj_tag(v___x_3451_) == 0 {
                        v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
                        lean_inc_n(v_a_3452_, 2);
                        lean_dec_ref_known(v___x_3451_, 1);
                        v___f_3453_ = lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3453_, 0, v_type_3428_);
                        lean_closure_set(v___f_3453_, 1, v_a_3452_);
                        v___x_3454_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3454_, v___f_3453_, v_a_3429_);
                        if lean_obj_tag(v___x_3455_) == 0 {
                            v_isSharedCheck_3462_ = (!lean_is_exclusive(v___x_3455_)) as u8;
                            if v_isSharedCheck_3462_ == 0 {
                                v_unused_3463_ = lean_ctor_get(v___x_3455_, 0);
                                lean_dec(v_unused_3463_);
                                v___x_3457_ = v___x_3455_;
                                v_isShared_3458_ = v_isSharedCheck_3462_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3455_);
                                v___x_3457_ = lean_box(0);
                                v_isShared_3458_ = v_isSharedCheck_3462_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3452_);
                            v_a_3464_ = lean_ctor_get(v___x_3455_, 0);
                            v_isSharedCheck_3471_ = (!lean_is_exclusive(v___x_3455_)) as u8;
                            if v_isSharedCheck_3471_ == 0 {
                                v___x_3466_ = v___x_3455_;
                                v_isShared_3467_ = v_isSharedCheck_3471_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3464_);
                                lean_dec(v___x_3455_);
                                v___x_3466_ = lean_box(0);
                                v_isShared_3467_ = v_isSharedCheck_3471_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_3428_);
                        return v___x_3451_;
                    }
                }
            }
            2 => {
                return v___x_3449_;
            }
            3 => {
                if v_isShared_3458_ == 0 {
                    lean_ctor_set(v___x_3457_, 0, v_a_3452_);
                    v___x_3460_ = v___x_3457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3452_);
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
                    v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
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
                    v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
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
    mut v_type_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
    mut v_a_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
    mut v_a_3488_: *mut LeanObject,
    mut v_a_3489_: *mut LeanObject,
    mut v_a_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3493_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3491_);
    lean_dec_ref(v_a_3490_);
    lean_dec(v_a_3489_);
    lean_dec_ref(v_a_3488_);
    lean_dec(v_a_3487_);
    lean_dec_ref(v_a_3486_);
    lean_dec(v_a_3485_);
    lean_dec_ref(v_a_3484_);
    lean_dec(v_a_3483_);
    lean_dec(v_a_3482_);
    return v_res_3493_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(
    mut v___x_3494_: *mut LeanObject,
    mut v_s_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3509_: u8 = 0;
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3496_ = lean_ctor_get(v_s_3495_, 0);
                v_typeIdOf_3497_ = lean_ctor_get(v_s_3495_, 1);
                v_exprToRingId_3498_ = lean_ctor_get(v_s_3495_, 2);
                v_semirings_3499_ = lean_ctor_get(v_s_3495_, 3);
                v_stypeIdOf_3500_ = lean_ctor_get(v_s_3495_, 4);
                v_exprToSemiringId_3501_ = lean_ctor_get(v_s_3495_, 5);
                v_ncRings_3502_ = lean_ctor_get(v_s_3495_, 6);
                v_exprToNCRingId_3503_ = lean_ctor_get(v_s_3495_, 7);
                v_nctypeIdOf_3504_ = lean_ctor_get(v_s_3495_, 8);
                v_ncSemirings_3505_ = lean_ctor_get(v_s_3495_, 9);
                v_exprToNCSemiringId_3506_ = lean_ctor_get(v_s_3495_, 10);
                v_ncstypeIdOf_3507_ = lean_ctor_get(v_s_3495_, 11);
                v_steps_3508_ = lean_ctor_get(v_s_3495_, 12);
                v_reportedMaxDegreeIssue_3509_ = lean_ctor_get_uint8(
                    v_s_3495_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3517_ = (!lean_is_exclusive(v_s_3495_)) as u8;
                if v_isSharedCheck_3517_ == 0 {
                    v___x_3511_ = v_s_3495_;
                    v_isShared_3512_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3508_);
                    lean_inc(v_ncstypeIdOf_3507_);
                    lean_inc(v_exprToNCSemiringId_3506_);
                    lean_inc(v_ncSemirings_3505_);
                    lean_inc(v_nctypeIdOf_3504_);
                    lean_inc(v_exprToNCRingId_3503_);
                    lean_inc(v_ncRings_3502_);
                    lean_inc(v_exprToSemiringId_3501_);
                    lean_inc(v_stypeIdOf_3500_);
                    lean_inc(v_semirings_3499_);
                    lean_inc(v_exprToRingId_3498_);
                    lean_inc(v_typeIdOf_3497_);
                    lean_inc(v_rings_3496_);
                    lean_dec(v_s_3495_);
                    v___x_3511_ = lean_box(0);
                    v_isShared_3512_ = v_isSharedCheck_3517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3513_ = lean_array_push(v_ncSemirings_3505_, v___x_3494_);
                if v_isShared_3512_ == 0 {
                    lean_ctor_set(v___x_3511_, 9, v___x_3513_);
                    v___x_3515_ = v___x_3511_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_rings_3496_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_typeIdOf_3497_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_exprToRingId_3498_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 3, v_semirings_3499_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 4, v_stypeIdOf_3500_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 5, v_exprToSemiringId_3501_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 6, v_ncRings_3502_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 7, v_exprToNCRingId_3503_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 8, v_nctypeIdOf_3504_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 9, v___x_3513_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 10, v_exprToNCSemiringId_3506_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 11, v_ncstypeIdOf_3507_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 12, v_steps_3508_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3516_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_type_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v_val_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3566_: u8 = 0;
    let mut v_unused_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3575_: u8 = 0;
    let mut v_a_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_a_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_a_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_3523_);
                v___x_3530_ = l_Lean_Meta_getDecLevel(
                    v_type_3523_,
                    v_a_3525_,
                    v_a_3526_,
                    v_a_3527_,
                    v_a_3528_,
                );
                if lean_obj_tag(v___x_3530_) == 0 {
                    v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
                    lean_inc_n(v_a_3531_, 2);
                    lean_dec_ref_known(v___x_3530_, 1);
                    v___x_3532_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___closed__1;
                    v___x_3533_ = lean_box(0);
                    v___x_3534_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3534_, 0, v_a_3531_);
                    lean_ctor_set(v___x_3534_, 1, v___x_3533_);
                    v___x_3535_ = l_Lean_mkConst(v___x_3532_, v___x_3534_);
                    lean_inc_ref(v_type_3523_);
                    v___x_3536_ = l_Lean_Expr_app___override(v___x_3535_, v_type_3523_);
                    v___x_3537_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3536_,
                        v_a_3525_,
                        v_a_3526_,
                        v_a_3527_,
                        v_a_3528_,
                    );
                    if lean_obj_tag(v___x_3537_) == 0 {
                        v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3589_ = (!lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v___x_3540_ = v___x_3537_;
                            v_isShared_3541_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3538_);
                            lean_dec(v___x_3537_);
                            v___x_3540_ = lean_box(0);
                            v_isShared_3541_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3531_);
                        lean_dec_ref(v_type_3523_);
                        v_a_3590_ = lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3597_ = (!lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3597_ == 0 {
                            v___x_3592_ = v___x_3537_;
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3590_);
                            lean_dec(v___x_3537_);
                            v___x_3592_ = lean_box(0);
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3523_);
                    v_a_3598_ = lean_ctor_get(v___x_3530_, 0);
                    v_isSharedCheck_3605_ = (!lean_is_exclusive(v___x_3530_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3530_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3598_);
                        lean_dec(v___x_3530_);
                        v___x_3600_ = lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3538_) == 1 {
                    lean_del_object(v___x_3540_);
                    v_val_3542_ = lean_ctor_get(v_a_3538_, 0);
                    v_isSharedCheck_3584_ = (!lean_is_exclusive(v_a_3538_)) as u8;
                    if v_isSharedCheck_3584_ == 0 {
                        v___x_3544_ = v_a_3538_;
                        v_isShared_3545_ = v_isSharedCheck_3584_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3542_);
                        lean_dec(v_a_3538_);
                        v___x_3544_ = lean_box(0);
                        v_isShared_3545_ = v_isSharedCheck_3584_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3538_);
                    lean_dec(v_a_3531_);
                    lean_dec_ref(v_type_3523_);
                    v___x_3585_ = lean_box(0);
                    if v_isShared_3541_ == 0 {
                        lean_ctor_set(v___x_3540_, 0, v___x_3585_);
                        v___x_3587_ = v___x_3540_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
                        v___x_3587_ = v_reuseFailAlloc_3588_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3546_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3524_, v_a_3527_);
                if lean_obj_tag(v___x_3546_) == 0 {
                    v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
                    lean_inc(v_a_3547_);
                    lean_dec_ref_known(v___x_3546_, 1);
                    v_ncSemirings_3548_ = lean_ctor_get(v_a_3547_, 9);
                    lean_inc_ref(v_ncSemirings_3548_);
                    lean_dec(v_a_3547_);
                    v___x_3549_ = lean_array_get_size(v_ncSemirings_3548_);
                    lean_dec_ref(v_ncSemirings_3548_);
                    v___x_3550_ = lean_box(0);
                    v___x_3551_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__7);
                    v___x_3552_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__15);
                    v___x_3553_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v___x_3553_, 0, v___x_3549_);
                    lean_ctor_set(v___x_3553_, 1, v_type_3523_);
                    lean_ctor_set(v___x_3553_, 2, v_a_3531_);
                    lean_ctor_set(v___x_3553_, 3, v_val_3542_);
                    lean_ctor_set(v___x_3553_, 4, v___x_3550_);
                    lean_ctor_set(v___x_3553_, 5, v___x_3550_);
                    lean_ctor_set(v___x_3553_, 6, v___x_3550_);
                    lean_ctor_set(v___x_3553_, 7, v___x_3550_);
                    lean_ctor_set(v___x_3553_, 8, v___x_3551_);
                    lean_ctor_set(v___x_3553_, 9, v___x_3552_);
                    lean_ctor_set(v___x_3553_, 10, v___x_3551_);
                    v___f_3554_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_3554_, 0, v___x_3553_);
                    v___x_3555_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3556_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3555_, v___f_3554_, v_a_3524_);
                    if lean_obj_tag(v___x_3556_) == 0 {
                        v_isSharedCheck_3566_ = (!lean_is_exclusive(v___x_3556_)) as u8;
                        if v_isSharedCheck_3566_ == 0 {
                            v_unused_3567_ = lean_ctor_get(v___x_3556_, 0);
                            lean_dec(v_unused_3567_);
                            v___x_3558_ = v___x_3556_;
                            v_isShared_3559_ = v_isSharedCheck_3566_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_3556_);
                            v___x_3558_ = lean_box(0);
                            v_isShared_3559_ = v_isSharedCheck_3566_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3544_);
                        v_a_3568_ = lean_ctor_get(v___x_3556_, 0);
                        v_isSharedCheck_3575_ = (!lean_is_exclusive(v___x_3556_)) as u8;
                        if v_isSharedCheck_3575_ == 0 {
                            v___x_3570_ = v___x_3556_;
                            v_isShared_3571_ = v_isSharedCheck_3575_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3568_);
                            lean_dec(v___x_3556_);
                            v___x_3570_ = lean_box(0);
                            v_isShared_3571_ = v_isSharedCheck_3575_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3544_);
                    lean_dec(v_val_3542_);
                    lean_dec(v_a_3531_);
                    lean_dec_ref(v_type_3523_);
                    v_a_3576_ = lean_ctor_get(v___x_3546_, 0);
                    v_isSharedCheck_3583_ = (!lean_is_exclusive(v___x_3546_)) as u8;
                    if v_isSharedCheck_3583_ == 0 {
                        v___x_3578_ = v___x_3546_;
                        v_isShared_3579_ = v_isSharedCheck_3583_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3576_);
                        lean_dec(v___x_3546_);
                        v___x_3578_ = lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3583_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3545_ == 0 {
                    lean_ctor_set(v___x_3544_, 0, v___x_3549_);
                    v___x_3561_ = v___x_3544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3549_);
                    v___x_3561_ = v_reuseFailAlloc_3565_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3559_ == 0 {
                    lean_ctor_set(v___x_3558_, 0, v___x_3561_);
                    v___x_3563_ = v___x_3558_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
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
                    v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
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
                    v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
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
                    v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
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
                    v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
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
    mut v_type_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_res_3613_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
    lean_dec(v_a_3611_);
    lean_dec_ref(v_a_3610_);
    lean_dec(v_a_3609_);
    lean_dec_ref(v_a_3608_);
    lean_dec(v_a_3607_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(
    mut v_type_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_a_3618_: *mut LeanObject,
    mut v_a_3619_: *mut LeanObject,
    mut v_a_3620_: *mut LeanObject,
    mut v_a_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3614_, v_a_3615_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
    return v___x_3626_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(
    mut v_type_3627_: *mut LeanObject,
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
    v_res_3639_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
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
    return v_res_3639_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(
    mut v_type_3640_: *mut LeanObject,
    mut v_a_3641_: *mut LeanObject,
    mut v_s_3642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rings_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3656_: u8 = 0;
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3643_ = lean_ctor_get(v_s_3642_, 0);
                v_typeIdOf_3644_ = lean_ctor_get(v_s_3642_, 1);
                v_exprToRingId_3645_ = lean_ctor_get(v_s_3642_, 2);
                v_semirings_3646_ = lean_ctor_get(v_s_3642_, 3);
                v_stypeIdOf_3647_ = lean_ctor_get(v_s_3642_, 4);
                v_exprToSemiringId_3648_ = lean_ctor_get(v_s_3642_, 5);
                v_ncRings_3649_ = lean_ctor_get(v_s_3642_, 6);
                v_exprToNCRingId_3650_ = lean_ctor_get(v_s_3642_, 7);
                v_nctypeIdOf_3651_ = lean_ctor_get(v_s_3642_, 8);
                v_ncSemirings_3652_ = lean_ctor_get(v_s_3642_, 9);
                v_exprToNCSemiringId_3653_ = lean_ctor_get(v_s_3642_, 10);
                v_ncstypeIdOf_3654_ = lean_ctor_get(v_s_3642_, 11);
                v_steps_3655_ = lean_ctor_get(v_s_3642_, 12);
                v_reportedMaxDegreeIssue_3656_ = lean_ctor_get_uint8(
                    v_s_3642_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_3664_ = (!lean_is_exclusive(v_s_3642_)) as u8;
                if v_isSharedCheck_3664_ == 0 {
                    v___x_3658_ = v_s_3642_;
                    v_isShared_3659_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_steps_3655_);
                    lean_inc(v_ncstypeIdOf_3654_);
                    lean_inc(v_exprToNCSemiringId_3653_);
                    lean_inc(v_ncSemirings_3652_);
                    lean_inc(v_nctypeIdOf_3651_);
                    lean_inc(v_exprToNCRingId_3650_);
                    lean_inc(v_ncRings_3649_);
                    lean_inc(v_exprToSemiringId_3648_);
                    lean_inc(v_stypeIdOf_3647_);
                    lean_inc(v_semirings_3646_);
                    lean_inc(v_exprToRingId_3645_);
                    lean_inc(v_typeIdOf_3644_);
                    lean_inc(v_rings_3643_);
                    lean_dec(v_s_3642_);
                    v___x_3658_ = lean_box(0);
                    v_isShared_3659_ = v_isSharedCheck_3664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3660_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_3654_, v_type_3640_, v_a_3641_);
                if v_isShared_3659_ == 0 {
                    lean_ctor_set(v___x_3658_, 11, v___x_3660_);
                    v___x_3662_ = v___x_3658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 13, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_rings_3643_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_typeIdOf_3644_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_exprToRingId_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_semirings_3646_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 4, v_stypeIdOf_3647_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 5, v_exprToSemiringId_3648_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 6, v_ncRings_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 7, v_exprToNCRingId_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 8, v_nctypeIdOf_3651_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 9, v_ncSemirings_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 10, v_exprToNCSemiringId_3653_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 11, v___x_3660_);
                    lean_ctor_set(v_reuseFailAlloc_3663_, 12, v_steps_3655_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3663_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
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
    mut v_type_3665_: *mut LeanObject,
    mut v_a_3666_: *mut LeanObject,
    mut v_a_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
    mut v_a_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v_ncstypeIdOf_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_unused_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3699_: u8 = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_a_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3672_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3666_, v_a_3669_);
                if lean_obj_tag(v___x_3672_) == 0 {
                    v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3704_ = (!lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3704_ == 0 {
                        v___x_3675_ = v___x_3672_;
                        v_isShared_3676_ = v_isSharedCheck_3704_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3673_);
                        lean_dec(v___x_3672_);
                        v___x_3675_ = lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3704_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3665_);
                    v_a_3705_ = lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3712_ = (!lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3712_ == 0 {
                        v___x_3707_ = v___x_3672_;
                        v_isShared_3708_ = v_isSharedCheck_3712_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3705_);
                        lean_dec(v___x_3672_);
                        v___x_3707_ = lean_box(0);
                        v_isShared_3708_ = v_isSharedCheck_3712_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_ncstypeIdOf_3677_ = lean_ctor_get(v_a_3673_, 11);
                lean_inc_ref(v_ncstypeIdOf_3677_);
                lean_dec(v_a_3673_);
                v___x_3678_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_3677_, v_type_3665_);
                lean_dec_ref(v_ncstypeIdOf_3677_);
                if lean_obj_tag(v___x_3678_) == 1 {
                    lean_dec_ref(v_type_3665_);
                    v_val_3679_ = lean_ctor_get(v___x_3678_, 0);
                    lean_inc(v_val_3679_);
                    lean_dec_ref_known(v___x_3678_, 1);
                    if v_isShared_3676_ == 0 {
                        lean_ctor_set(v___x_3675_, 0, v_val_3679_);
                        v___x_3681_ = v___x_3675_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_val_3679_);
                        v___x_3681_ = v_reuseFailAlloc_3682_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3678_);
                    lean_del_object(v___x_3675_);
                    lean_inc_ref(v_type_3665_);
                    v___x_3683_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
                    if lean_obj_tag(v___x_3683_) == 0 {
                        v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
                        lean_inc_n(v_a_3684_, 2);
                        lean_dec_ref_known(v___x_3683_, 1);
                        v___f_3685_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                        lean_closure_set(v___f_3685_, 0, v_type_3665_);
                        lean_closure_set(v___f_3685_, 1, v_a_3684_);
                        v___x_3686_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3687_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3686_, v___f_3685_, v_a_3666_);
                        if lean_obj_tag(v___x_3687_) == 0 {
                            v_isSharedCheck_3694_ = (!lean_is_exclusive(v___x_3687_)) as u8;
                            if v_isSharedCheck_3694_ == 0 {
                                v_unused_3695_ = lean_ctor_get(v___x_3687_, 0);
                                lean_dec(v_unused_3695_);
                                v___x_3689_ = v___x_3687_;
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3687_);
                                v___x_3689_ = lean_box(0);
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3684_);
                            v_a_3696_ = lean_ctor_get(v___x_3687_, 0);
                            v_isSharedCheck_3703_ = (!lean_is_exclusive(v___x_3687_)) as u8;
                            if v_isSharedCheck_3703_ == 0 {
                                v___x_3698_ = v___x_3687_;
                                v_isShared_3699_ = v_isSharedCheck_3703_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3696_);
                                lean_dec(v___x_3687_);
                                v___x_3698_ = lean_box(0);
                                v_isShared_3699_ = v_isSharedCheck_3703_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_3665_);
                        return v___x_3683_;
                    }
                }
            }
            2 => {
                return v___x_3681_;
            }
            3 => {
                if v_isShared_3690_ == 0 {
                    lean_ctor_set(v___x_3689_, 0, v_a_3684_);
                    v___x_3692_ = v___x_3689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3684_);
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
                    v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
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
                    v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
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
    mut v_type_3713_: *mut LeanObject,
    mut v_a_3714_: *mut LeanObject,
    mut v_a_3715_: *mut LeanObject,
    mut v_a_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
    mut v_a_3718_: *mut LeanObject,
    mut v_a_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3720_: *mut LeanObject = core::ptr::null_mut();
    v_res_3720_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(
        v_type_3713_,
        v_a_3714_,
        v_a_3715_,
        v_a_3716_,
        v_a_3717_,
        v_a_3718_,
    );
    lean_dec(v_a_3718_);
    lean_dec_ref(v_a_3717_);
    lean_dec(v_a_3716_);
    lean_dec_ref(v_a_3715_);
    lean_dec(v_a_3714_);
    return v_res_3720_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(
    mut v_type_3721_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_type_3734_: *mut LeanObject,
    mut v_a_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
    mut v_a_3737_: *mut LeanObject,
    mut v_a_3738_: *mut LeanObject,
    mut v_a_3739_: *mut LeanObject,
    mut v_a_3740_: *mut LeanObject,
    mut v_a_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
    mut v_a_3743_: *mut LeanObject,
    mut v_a_3744_: *mut LeanObject,
    mut v_a_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3744_);
    lean_dec_ref(v_a_3743_);
    lean_dec(v_a_3742_);
    lean_dec_ref(v_a_3741_);
    lean_dec(v_a_3740_);
    lean_dec_ref(v_a_3739_);
    lean_dec(v_a_3738_);
    lean_dec_ref(v_a_3737_);
    lean_dec(v_a_3736_);
    lean_dec(v_a_3735_);
    return v_res_3746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(
    builtin: u8,
) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
}
