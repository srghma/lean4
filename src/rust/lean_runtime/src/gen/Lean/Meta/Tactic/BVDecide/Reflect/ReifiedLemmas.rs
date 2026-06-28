// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr6};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVLogical::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVPred::l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 109, 109, 97, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value) as *mut LeanObject,1655553077289932752 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value) as *mut LeanObject,16093780639914376387 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value) as *mut LeanObject,9753356465987597394 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value) as *mut LeanObject,13145409667090857818 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 111, 110, 100, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value) as *mut LeanObject,403369037444587699 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value) as *mut LeanObject,4680477061952437575 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 100, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value) as *mut LeanObject,403369037444587699 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value) as *mut LeanObject,15891626368152809914 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(
    mut v_expr_573_: *mut LeanObject,
    mut v_a_574_: *mut LeanObject,
    mut v_lhs_575_: *mut LeanObject,
    mut v_lemmaName_576_: *mut LeanObject,
    mut v___x_577_: *mut LeanObject,
    mut v_discrExpr_578_: *mut LeanObject,
    mut v_lhsExpr_579_: *mut LeanObject,
    mut v_rhsExpr_580_: *mut LeanObject,
    mut v___x_581_: *mut LeanObject,
    mut v___x_582_: *mut LeanObject,
    mut v___x_583_: *mut LeanObject,
    mut v___x_584_: *mut LeanObject,
    mut v___x_585_: *mut LeanObject,
    mut v___x_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___y_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_width_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_615_: u8 = 0;
    let mut v_a_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_619_: u8 = 0;
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_593_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_573_,
                    v___y_587_,
                    v___y_588_,
                    v___y_589_,
                    v___y_590_,
                    v___y_591_,
                );
                if lean_obj_tag(v___x_593_) == 0 {
                    v_a_594_ = lean_ctor_get(v___x_593_, 0);
                    lean_inc(v_a_594_);
                    lean_dec_ref_known(v___x_593_, 1);
                    v___x_595_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                        v_a_574_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_,
                    );
                    if lean_obj_tag(v___x_595_) == 0 {
                        v_a_596_ = lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_615_ = (!lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_615_ == 0 {
                            v___x_598_ = v___x_595_;
                            v_isShared_599_ = v_isSharedCheck_615_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_596_);
                            lean_dec(v___x_595_);
                            v___x_598_ = lean_box(0);
                            v_isShared_599_ = v_isSharedCheck_615_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_594_);
                        lean_dec_ref(v___x_586_);
                        lean_dec_ref(v___x_585_);
                        lean_dec_ref(v___x_584_);
                        lean_dec_ref(v___x_583_);
                        lean_dec_ref(v___x_582_);
                        lean_dec_ref(v___x_581_);
                        lean_dec_ref(v_rhsExpr_580_);
                        lean_dec_ref(v_lhsExpr_579_);
                        lean_dec_ref(v_discrExpr_578_);
                        lean_dec(v___x_577_);
                        lean_dec(v_lemmaName_576_);
                        lean_dec_ref(v_lhs_575_);
                        v_a_616_ = lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_623_ = (!lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_623_ == 0 {
                            v___x_618_ = v___x_595_;
                            v_isShared_619_ = v_isSharedCheck_623_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_616_);
                            lean_dec(v___x_595_);
                            v___x_618_ = lean_box(0);
                            v_isShared_619_ = v_isSharedCheck_623_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_586_);
                    lean_dec_ref(v___x_585_);
                    lean_dec_ref(v___x_584_);
                    lean_dec_ref(v___x_583_);
                    lean_dec_ref(v___x_582_);
                    lean_dec_ref(v___x_581_);
                    lean_dec_ref(v_rhsExpr_580_);
                    lean_dec_ref(v_lhsExpr_579_);
                    lean_dec_ref(v_discrExpr_578_);
                    lean_dec(v___x_577_);
                    lean_dec(v_lemmaName_576_);
                    lean_dec_ref(v_lhs_575_);
                    lean_dec_ref(v_a_574_);
                    return v___x_593_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_596_) == 0 {
                    lean_inc(v_a_594_);
                    v___x_613_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_594_);
                    v___y_601_ = v___x_613_;
                    state = 2;
                    continue;
                } else {
                    v_val_614_ = lean_ctor_get(v_a_596_, 0);
                    lean_inc(v_val_614_);
                    lean_dec_ref_known(v_a_596_, 1);
                    v___y_601_ = v_val_614_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_width_602_ = lean_ctor_get(v_lhs_575_, 0);
                lean_inc(v_width_602_);
                lean_dec_ref(v_lhs_575_);
                lean_inc(v___x_577_);
                v___x_603_ = l_Lean_mkConst(v_lemmaName_576_, v___x_577_);
                v___x_604_ = l_Lean_mkNatLit(v_width_602_);
                v___x_605_ = l_Lean_mkApp4(
                    v___x_603_,
                    v___x_604_,
                    v_discrExpr_578_,
                    v_lhsExpr_579_,
                    v_rhsExpr_580_,
                );
                v___x_606_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0;
                v___x_607_ = l_Lean_Name_mkStr6(
                    v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_606_,
                );
                v___x_608_ = l_Lean_mkConst(v___x_607_, v___x_577_);
                v___x_609_ =
                    l_Lean_mkApp4(v___x_608_, v___x_586_, v_a_594_, v___y_601_, v___x_605_);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 0, v___x_609_);
                    v___x_611_ = v___x_598_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
                    v___x_611_ = v_reuseFailAlloc_612_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_611_;
            }
            4 => {
                if v_isShared_619_ == 0 {
                    v___x_621_ = v___x_618_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
                    v___x_621_ = v_reuseFailAlloc_622_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_624_: *mut LeanObject = *_args.add(0);
    let mut v_a_625_: *mut LeanObject = *_args.add(1);
    let mut v_lhs_626_: *mut LeanObject = *_args.add(2);
    let mut v_lemmaName_627_: *mut LeanObject = *_args.add(3);
    let mut v___x_628_: *mut LeanObject = *_args.add(4);
    let mut v_discrExpr_629_: *mut LeanObject = *_args.add(5);
    let mut v_lhsExpr_630_: *mut LeanObject = *_args.add(6);
    let mut v_rhsExpr_631_: *mut LeanObject = *_args.add(7);
    let mut v___x_632_: *mut LeanObject = *_args.add(8);
    let mut v___x_633_: *mut LeanObject = *_args.add(9);
    let mut v___x_634_: *mut LeanObject = *_args.add(10);
    let mut v___x_635_: *mut LeanObject = *_args.add(11);
    let mut v___x_636_: *mut LeanObject = *_args.add(12);
    let mut v___x_637_: *mut LeanObject = *_args.add(13);
    let mut v___y_638_: *mut LeanObject = *_args.add(14);
    let mut v___y_639_: *mut LeanObject = *_args.add(15);
    let mut v___y_640_: *mut LeanObject = *_args.add(16);
    let mut v___y_641_: *mut LeanObject = *_args.add(17);
    let mut v___y_642_: *mut LeanObject = *_args.add(18);
    let mut v___y_643_: *mut LeanObject = *_args.add(19);
    let mut v_res_644_: *mut LeanObject = core::ptr::null_mut();
    v_res_644_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(v_expr_624_, v_a_625_, v_lhs_626_, v_lemmaName_627_, v___x_628_, v_discrExpr_629_, v_lhsExpr_630_, v_rhsExpr_631_, v___x_632_, v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
    lean_dec(v___y_642_);
    lean_dec_ref(v___y_641_);
    lean_dec(v___y_640_);
    lean_dec_ref(v___y_639_);
    lean_dec(v___y_638_);
    return v_res_644_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    v___x_650_ = lean_box(0);
    v___x_651_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2;
    v___x_652_ = l_Lean_mkConst(v___x_651_, v___x_650_);
    return v___x_652_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = lean_box(0);
    v___x_663_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8;
    v___x_664_ = l_Lean_mkConst(v___x_663_, v___x_662_);
    return v___x_664_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(
    mut v_discr_678_: *mut LeanObject,
    mut v_atom_679_: *mut LeanObject,
    mut v_lhs_680_: *mut LeanObject,
    mut v_discrExpr_681_: *mut LeanObject,
    mut v_atomExpr_682_: *mut LeanObject,
    mut v_lhsExpr_683_: *mut LeanObject,
    mut v_rhsExpr_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_notDiscrExpr_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_708_: u8 = 0;
    let mut v_val_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_bvExpr_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lemmaName_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut v_a_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v_a_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_750_: u8 = 0;
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_754_: u8 = 0;
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_760_: u8 = 0;
    let mut v_a_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_768_: u8 = 0;
    let mut v_a_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_776_: u8 = 0;
    let mut v_a_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_690_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0;
                v___x_691_ = lean_box(0);
                v___x_692_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3);
                lean_inc_ref_n(v_discrExpr_681_, 2);
                v_notDiscrExpr_693_ = l_Lean_Expr_app___override(v___x_692_, v_discrExpr_681_);
                lean_inc_ref(v_notDiscrExpr_693_);
                v___x_694_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(
                    v_discr_678_,
                    v_discrExpr_681_,
                    v_notDiscrExpr_693_,
                );
                if lean_obj_tag(v___x_694_) == 0 {
                    v_a_695_ = lean_ctor_get(v___x_694_, 0);
                    lean_inc(v_a_695_);
                    lean_dec_ref_known(v___x_694_, 1);
                    v___x_696_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6;
                    v___x_697_ = lean_unsigned_to_nat(2);
                    v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
                    lean_inc_ref(v_atomExpr_682_);
                    v___x_699_ = lean_array_push(v___x_698_, v_atomExpr_682_);
                    lean_inc_ref(v_lhsExpr_683_);
                    v___x_700_ = lean_array_push(v___x_699_, v_lhsExpr_683_);
                    v___x_701_ = l_Lean_Meta_mkAppM(
                        v___x_696_, v___x_700_, v_a_685_, v_a_686_, v_a_687_, v_a_688_,
                    );
                    if lean_obj_tag(v___x_701_) == 0 {
                        v_a_702_ = lean_ctor_get(v___x_701_, 0);
                        lean_inc_n(v_a_702_, 2);
                        lean_dec_ref_known(v___x_701_, 1);
                        v___x_703_ = 0;
                        lean_inc_ref(v_lhsExpr_683_);
                        lean_inc_ref(v_lhs_680_);
                        v___x_704_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
                            v_atom_679_,
                            v_lhs_680_,
                            v_atomExpr_682_,
                            v_lhsExpr_683_,
                            v___x_703_,
                            v_a_702_,
                        );
                        if lean_obj_tag(v___x_704_) == 0 {
                            v_a_705_ = lean_ctor_get(v___x_704_, 0);
                            v_isSharedCheck_760_ = (!lean_is_exclusive(v___x_704_)) as u8;
                            if v_isSharedCheck_760_ == 0 {
                                v___x_707_ = v___x_704_;
                                v_isShared_708_ = v_isSharedCheck_760_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_705_);
                                lean_dec(v___x_704_);
                                v___x_707_ = lean_box(0);
                                v_isShared_708_ = v_isSharedCheck_760_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_702_);
                            lean_dec(v_a_695_);
                            lean_dec_ref(v_notDiscrExpr_693_);
                            lean_dec_ref(v_rhsExpr_684_);
                            lean_dec_ref(v_lhsExpr_683_);
                            lean_dec_ref(v_discrExpr_681_);
                            lean_dec_ref(v_lhs_680_);
                            v_a_761_ = lean_ctor_get(v___x_704_, 0);
                            v_isSharedCheck_768_ = (!lean_is_exclusive(v___x_704_)) as u8;
                            if v_isSharedCheck_768_ == 0 {
                                v___x_763_ = v___x_704_;
                                v_isShared_764_ = v_isSharedCheck_768_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_761_);
                                lean_dec(v___x_704_);
                                v___x_763_ = lean_box(0);
                                v_isShared_764_ = v_isSharedCheck_768_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_695_);
                        lean_dec_ref(v_notDiscrExpr_693_);
                        lean_dec_ref(v_rhsExpr_684_);
                        lean_dec_ref(v_lhsExpr_683_);
                        lean_dec_ref(v_atomExpr_682_);
                        lean_dec_ref(v_discrExpr_681_);
                        lean_dec_ref(v_lhs_680_);
                        lean_dec_ref(v_atom_679_);
                        v_a_769_ = lean_ctor_get(v___x_701_, 0);
                        v_isSharedCheck_776_ = (!lean_is_exclusive(v___x_701_)) as u8;
                        if v_isSharedCheck_776_ == 0 {
                            v___x_771_ = v___x_701_;
                            v_isShared_772_ = v_isSharedCheck_776_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_769_);
                            lean_dec(v___x_701_);
                            v___x_771_ = lean_box(0);
                            v_isShared_772_ = v_isSharedCheck_776_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_notDiscrExpr_693_);
                    lean_dec_ref(v_rhsExpr_684_);
                    lean_dec_ref(v_lhsExpr_683_);
                    lean_dec_ref(v_atomExpr_682_);
                    lean_dec_ref(v_discrExpr_681_);
                    lean_dec_ref(v_lhs_680_);
                    lean_dec_ref(v_atom_679_);
                    v_a_777_ = lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_784_ = (!lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_784_ == 0 {
                        v___x_779_ = v___x_694_;
                        v_isShared_780_ = v_isSharedCheck_784_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_777_);
                        lean_dec(v___x_694_);
                        v___x_779_ = lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_784_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_705_) == 1 {
                    lean_del_object(v___x_707_);
                    v_val_709_ = lean_ctor_get(v_a_705_, 0);
                    v_isSharedCheck_755_ = (!lean_is_exclusive(v_a_705_)) as u8;
                    if v_isSharedCheck_755_ == 0 {
                        v___x_711_ = v_a_705_;
                        v_isShared_712_ = v_isSharedCheck_755_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_709_);
                        lean_dec(v_a_705_);
                        v___x_711_ = lean_box(0);
                        v_isShared_712_ = v_isSharedCheck_755_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_705_);
                    lean_dec(v_a_702_);
                    lean_dec(v_a_695_);
                    lean_dec_ref(v_notDiscrExpr_693_);
                    lean_dec_ref(v_rhsExpr_684_);
                    lean_dec_ref(v_lhsExpr_683_);
                    lean_dec_ref(v_discrExpr_681_);
                    lean_dec_ref(v_lhs_680_);
                    v___x_756_ = lean_box(0);
                    if v_isShared_708_ == 0 {
                        lean_ctor_set(v___x_707_, 0, v___x_756_);
                        v___x_758_ = v___x_707_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
                        v___x_758_ = v_reuseFailAlloc_759_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_713_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_709_);
                if lean_obj_tag(v___x_713_) == 0 {
                    v_a_714_ = lean_ctor_get(v___x_713_, 0);
                    lean_inc(v_a_714_);
                    lean_dec_ref_known(v___x_713_, 1);
                    v___x_715_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
                    lean_inc(v_a_702_);
                    lean_inc_ref(v_notDiscrExpr_693_);
                    v___x_716_ = l_Lean_mkAppB(v___x_715_, v_notDiscrExpr_693_, v_a_702_);
                    v___x_717_ = 3;
                    lean_inc_ref(v___x_716_);
                    v___x_718_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
                        v_a_695_,
                        v_a_714_,
                        v_notDiscrExpr_693_,
                        v_a_702_,
                        v___x_717_,
                        v___x_716_,
                    );
                    if lean_obj_tag(v___x_718_) == 0 {
                        v_a_719_ = lean_ctor_get(v___x_718_, 0);
                        v_isSharedCheck_738_ = (!lean_is_exclusive(v___x_718_)) as u8;
                        if v_isSharedCheck_738_ == 0 {
                            v___x_721_ = v___x_718_;
                            v_isShared_722_ = v_isSharedCheck_738_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_719_);
                            lean_dec(v___x_718_);
                            v___x_721_ = lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_738_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_716_);
                        lean_del_object(v___x_711_);
                        lean_dec_ref(v_rhsExpr_684_);
                        lean_dec_ref(v_lhsExpr_683_);
                        lean_dec_ref(v_discrExpr_681_);
                        lean_dec_ref(v_lhs_680_);
                        v_a_739_ = lean_ctor_get(v___x_718_, 0);
                        v_isSharedCheck_746_ = (!lean_is_exclusive(v___x_718_)) as u8;
                        if v_isSharedCheck_746_ == 0 {
                            v___x_741_ = v___x_718_;
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_739_);
                            lean_dec(v___x_718_);
                            v___x_741_ = lean_box(0);
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_711_);
                    lean_dec(v_a_702_);
                    lean_dec(v_a_695_);
                    lean_dec_ref(v_notDiscrExpr_693_);
                    lean_dec_ref(v_rhsExpr_684_);
                    lean_dec_ref(v_lhsExpr_683_);
                    lean_dec_ref(v_discrExpr_681_);
                    lean_dec_ref(v_lhs_680_);
                    v_a_747_ = lean_ctor_get(v___x_713_, 0);
                    v_isSharedCheck_754_ = (!lean_is_exclusive(v___x_713_)) as u8;
                    if v_isSharedCheck_754_ == 0 {
                        v___x_749_ = v___x_713_;
                        v_isShared_750_ = v_isSharedCheck_754_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_747_);
                        lean_dec(v___x_713_);
                        v___x_749_ = lean_box(0);
                        v_isShared_750_ = v_isSharedCheck_754_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_bvExpr_723_ = lean_ctor_get(v_a_719_, 0);
                lean_inc_ref(v_bvExpr_723_);
                v_expr_724_ = lean_ctor_get(v_a_719_, 3);
                lean_inc_ref_n(v_expr_724_, 2);
                v___x_725_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10;
                v___x_726_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11;
                v___x_727_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12;
                v___x_728_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13;
                v_lemmaName_729_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16;
                v___f_730_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed as *mut core::ffi::c_void, 20, 14);
                lean_closure_set(v___f_730_, 0, v_expr_724_);
                lean_closure_set(v___f_730_, 1, v_a_719_);
                lean_closure_set(v___f_730_, 2, v_lhs_680_);
                lean_closure_set(v___f_730_, 3, v_lemmaName_729_);
                lean_closure_set(v___f_730_, 4, v___x_691_);
                lean_closure_set(v___f_730_, 5, v_discrExpr_681_);
                lean_closure_set(v___f_730_, 6, v_lhsExpr_683_);
                lean_closure_set(v___f_730_, 7, v_rhsExpr_684_);
                lean_closure_set(v___f_730_, 8, v___x_725_);
                lean_closure_set(v___f_730_, 9, v___x_726_);
                lean_closure_set(v___f_730_, 10, v___x_727_);
                lean_closure_set(v___f_730_, 11, v___x_728_);
                lean_closure_set(v___f_730_, 12, v___x_690_);
                lean_closure_set(v___f_730_, 13, v___x_716_);
                v___x_731_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_731_, 0, v_bvExpr_723_);
                lean_ctor_set(v___x_731_, 1, v___f_730_);
                lean_ctor_set(v___x_731_, 2, v_expr_724_);
                if v_isShared_712_ == 0 {
                    lean_ctor_set(v___x_711_, 0, v___x_731_);
                    v___x_733_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
                    v___x_733_ = v_reuseFailAlloc_737_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_722_ == 0 {
                    lean_ctor_set(v___x_721_, 0, v___x_733_);
                    v___x_735_ = v___x_721_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
                    v___x_735_ = v_reuseFailAlloc_736_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_735_;
            }
            6 => {
                if v_isShared_742_ == 0 {
                    v___x_744_ = v___x_741_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_744_;
            }
            8 => {
                if v_isShared_750_ == 0 {
                    v___x_752_ = v___x_749_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
                    v___x_752_ = v_reuseFailAlloc_753_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_752_;
            }
            10 => {
                return v___x_758_;
            }
            11 => {
                if v_isShared_764_ == 0 {
                    v___x_766_ = v___x_763_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
                    v___x_766_ = v_reuseFailAlloc_767_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_766_;
            }
            13 => {
                if v_isShared_772_ == 0 {
                    v___x_774_ = v___x_771_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
                    v___x_774_ = v_reuseFailAlloc_775_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_774_;
            }
            15 => {
                if v_isShared_780_ == 0 {
                    v___x_782_ = v___x_779_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
                    v___x_782_ = v_reuseFailAlloc_783_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___boxed(
    mut v_discr_785_: *mut LeanObject,
    mut v_atom_786_: *mut LeanObject,
    mut v_lhs_787_: *mut LeanObject,
    mut v_discrExpr_788_: *mut LeanObject,
    mut v_atomExpr_789_: *mut LeanObject,
    mut v_lhsExpr_790_: *mut LeanObject,
    mut v_rhsExpr_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_785_, v_atom_786_, v_lhs_787_, v_discrExpr_788_, v_atomExpr_789_, v_lhsExpr_790_, v_rhsExpr_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
    lean_dec(v_a_795_);
    lean_dec_ref(v_a_794_);
    lean_dec(v_a_793_);
    lean_dec_ref(v_a_792_);
    return v_res_797_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(
    mut v_discr_798_: *mut LeanObject,
    mut v_atom_799_: *mut LeanObject,
    mut v_lhs_800_: *mut LeanObject,
    mut v_discrExpr_801_: *mut LeanObject,
    mut v_atomExpr_802_: *mut LeanObject,
    mut v_lhsExpr_803_: *mut LeanObject,
    mut v_rhsExpr_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_798_, v_atom_799_, v_lhs_800_, v_discrExpr_801_, v_atomExpr_802_, v_lhsExpr_803_, v_rhsExpr_804_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
    return v___x_811_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___boxed(
    mut v_discr_812_: *mut LeanObject,
    mut v_atom_813_: *mut LeanObject,
    mut v_lhs_814_: *mut LeanObject,
    mut v_discrExpr_815_: *mut LeanObject,
    mut v_atomExpr_816_: *mut LeanObject,
    mut v_lhsExpr_817_: *mut LeanObject,
    mut v_rhsExpr_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_825_: *mut LeanObject = core::ptr::null_mut();
    v_res_825_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(v_discr_812_, v_atom_813_, v_lhs_814_, v_discrExpr_815_, v_atomExpr_816_, v_lhsExpr_817_, v_rhsExpr_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
    lean_dec(v_a_823_);
    lean_dec_ref(v_a_822_);
    lean_dec(v_a_821_);
    lean_dec_ref(v_a_820_);
    lean_dec(v_a_819_);
    return v_res_825_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(
    mut v_expr_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_rhs_828_: *mut LeanObject,
    mut v_lemmaName_829_: *mut LeanObject,
    mut v___x_830_: *mut LeanObject,
    mut v_discrExpr_831_: *mut LeanObject,
    mut v_lhsExpr_832_: *mut LeanObject,
    mut v_rhsExpr_833_: *mut LeanObject,
    mut v___x_834_: *mut LeanObject,
    mut v___x_835_: *mut LeanObject,
    mut v___x_836_: *mut LeanObject,
    mut v___x_837_: *mut LeanObject,
    mut v___x_838_: *mut LeanObject,
    mut v___x_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
    mut v___y_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_852_: u8 = 0;
    let mut v___y_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_width_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_868_: u8 = 0;
    let mut v_a_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_846_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_826_,
                    v___y_840_,
                    v___y_841_,
                    v___y_842_,
                    v___y_843_,
                    v___y_844_,
                );
                if lean_obj_tag(v___x_846_) == 0 {
                    v_a_847_ = lean_ctor_get(v___x_846_, 0);
                    lean_inc(v_a_847_);
                    lean_dec_ref_known(v___x_846_, 1);
                    v___x_848_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                        v_a_827_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_,
                    );
                    if lean_obj_tag(v___x_848_) == 0 {
                        v_a_849_ = lean_ctor_get(v___x_848_, 0);
                        v_isSharedCheck_868_ = (!lean_is_exclusive(v___x_848_)) as u8;
                        if v_isSharedCheck_868_ == 0 {
                            v___x_851_ = v___x_848_;
                            v_isShared_852_ = v_isSharedCheck_868_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_849_);
                            lean_dec(v___x_848_);
                            v___x_851_ = lean_box(0);
                            v_isShared_852_ = v_isSharedCheck_868_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_847_);
                        lean_dec_ref(v___x_839_);
                        lean_dec_ref(v___x_838_);
                        lean_dec_ref(v___x_837_);
                        lean_dec_ref(v___x_836_);
                        lean_dec_ref(v___x_835_);
                        lean_dec_ref(v___x_834_);
                        lean_dec_ref(v_rhsExpr_833_);
                        lean_dec_ref(v_lhsExpr_832_);
                        lean_dec_ref(v_discrExpr_831_);
                        lean_dec(v___x_830_);
                        lean_dec(v_lemmaName_829_);
                        lean_dec_ref(v_rhs_828_);
                        v_a_869_ = lean_ctor_get(v___x_848_, 0);
                        v_isSharedCheck_876_ = (!lean_is_exclusive(v___x_848_)) as u8;
                        if v_isSharedCheck_876_ == 0 {
                            v___x_871_ = v___x_848_;
                            v_isShared_872_ = v_isSharedCheck_876_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_869_);
                            lean_dec(v___x_848_);
                            v___x_871_ = lean_box(0);
                            v_isShared_872_ = v_isSharedCheck_876_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_839_);
                    lean_dec_ref(v___x_838_);
                    lean_dec_ref(v___x_837_);
                    lean_dec_ref(v___x_836_);
                    lean_dec_ref(v___x_835_);
                    lean_dec_ref(v___x_834_);
                    lean_dec_ref(v_rhsExpr_833_);
                    lean_dec_ref(v_lhsExpr_832_);
                    lean_dec_ref(v_discrExpr_831_);
                    lean_dec(v___x_830_);
                    lean_dec(v_lemmaName_829_);
                    lean_dec_ref(v_rhs_828_);
                    lean_dec_ref(v_a_827_);
                    return v___x_846_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_849_) == 0 {
                    lean_inc(v_a_847_);
                    v___x_866_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_847_);
                    v___y_854_ = v___x_866_;
                    state = 2;
                    continue;
                } else {
                    v_val_867_ = lean_ctor_get(v_a_849_, 0);
                    lean_inc(v_val_867_);
                    lean_dec_ref_known(v_a_849_, 1);
                    v___y_854_ = v_val_867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_width_855_ = lean_ctor_get(v_rhs_828_, 0);
                lean_inc(v_width_855_);
                lean_dec_ref(v_rhs_828_);
                lean_inc(v___x_830_);
                v___x_856_ = l_Lean_mkConst(v_lemmaName_829_, v___x_830_);
                v___x_857_ = l_Lean_mkNatLit(v_width_855_);
                v___x_858_ = l_Lean_mkApp4(
                    v___x_856_,
                    v___x_857_,
                    v_discrExpr_831_,
                    v_lhsExpr_832_,
                    v_rhsExpr_833_,
                );
                v___x_859_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0;
                v___x_860_ = l_Lean_Name_mkStr6(
                    v___x_834_, v___x_835_, v___x_836_, v___x_837_, v___x_838_, v___x_859_,
                );
                v___x_861_ = l_Lean_mkConst(v___x_860_, v___x_830_);
                v___x_862_ =
                    l_Lean_mkApp4(v___x_861_, v___x_839_, v_a_847_, v___y_854_, v___x_858_);
                if v_isShared_852_ == 0 {
                    lean_ctor_set(v___x_851_, 0, v___x_862_);
                    v___x_864_ = v___x_851_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
                    v___x_864_ = v_reuseFailAlloc_865_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_864_;
            }
            4 => {
                if v_isShared_872_ == 0 {
                    v___x_874_ = v___x_871_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
                    v___x_874_ = v_reuseFailAlloc_875_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_877_: *mut LeanObject = *_args.add(0);
    let mut v_a_878_: *mut LeanObject = *_args.add(1);
    let mut v_rhs_879_: *mut LeanObject = *_args.add(2);
    let mut v_lemmaName_880_: *mut LeanObject = *_args.add(3);
    let mut v___x_881_: *mut LeanObject = *_args.add(4);
    let mut v_discrExpr_882_: *mut LeanObject = *_args.add(5);
    let mut v_lhsExpr_883_: *mut LeanObject = *_args.add(6);
    let mut v_rhsExpr_884_: *mut LeanObject = *_args.add(7);
    let mut v___x_885_: *mut LeanObject = *_args.add(8);
    let mut v___x_886_: *mut LeanObject = *_args.add(9);
    let mut v___x_887_: *mut LeanObject = *_args.add(10);
    let mut v___x_888_: *mut LeanObject = *_args.add(11);
    let mut v___x_889_: *mut LeanObject = *_args.add(12);
    let mut v___x_890_: *mut LeanObject = *_args.add(13);
    let mut v___y_891_: *mut LeanObject = *_args.add(14);
    let mut v___y_892_: *mut LeanObject = *_args.add(15);
    let mut v___y_893_: *mut LeanObject = *_args.add(16);
    let mut v___y_894_: *mut LeanObject = *_args.add(17);
    let mut v___y_895_: *mut LeanObject = *_args.add(18);
    let mut v___y_896_: *mut LeanObject = *_args.add(19);
    let mut v_res_897_: *mut LeanObject = core::ptr::null_mut();
    v_res_897_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(v_expr_877_, v_a_878_, v_rhs_879_, v_lemmaName_880_, v___x_881_, v_discrExpr_882_, v_lhsExpr_883_, v_rhsExpr_884_, v___x_885_, v___x_886_, v___x_887_, v___x_888_, v___x_889_, v___x_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
    lean_dec(v___y_895_);
    lean_dec_ref(v___y_894_);
    lean_dec(v___y_893_);
    lean_dec_ref(v___y_892_);
    lean_dec(v___y_891_);
    return v_res_897_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(
    mut v_discr_906_: *mut LeanObject,
    mut v_atom_907_: *mut LeanObject,
    mut v_rhs_908_: *mut LeanObject,
    mut v_discrExpr_909_: *mut LeanObject,
    mut v_atomExpr_910_: *mut LeanObject,
    mut v_lhsExpr_911_: *mut LeanObject,
    mut v_rhsExpr_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v_val_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_934_: u8 = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v_bvExpr_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lemmaName_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_962_: u8 = 0;
    let mut v_a_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_966_: u8 = 0;
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_a_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_978_: u8 = 0;
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut v_a_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_992_: u8 = 0;
    let mut v_a_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_918_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6;
                v___x_919_ = lean_unsigned_to_nat(2);
                v___x_920_ = lean_mk_empty_array_with_capacity(v___x_919_);
                lean_inc_ref(v_atomExpr_910_);
                v___x_921_ = lean_array_push(v___x_920_, v_atomExpr_910_);
                lean_inc_ref(v_rhsExpr_912_);
                v___x_922_ = lean_array_push(v___x_921_, v_rhsExpr_912_);
                v___x_923_ = l_Lean_Meta_mkAppM(
                    v___x_918_, v___x_922_, v_a_913_, v_a_914_, v_a_915_, v_a_916_,
                );
                if lean_obj_tag(v___x_923_) == 0 {
                    v_a_924_ = lean_ctor_get(v___x_923_, 0);
                    lean_inc_n(v_a_924_, 2);
                    lean_dec_ref_known(v___x_923_, 1);
                    v___x_925_ = 0;
                    lean_inc_ref(v_rhsExpr_912_);
                    lean_inc_ref(v_rhs_908_);
                    v___x_926_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
                        v_atom_907_,
                        v_rhs_908_,
                        v_atomExpr_910_,
                        v_rhsExpr_912_,
                        v___x_925_,
                        v_a_924_,
                    );
                    if lean_obj_tag(v___x_926_) == 0 {
                        v_a_927_ = lean_ctor_get(v___x_926_, 0);
                        v_isSharedCheck_984_ = (!lean_is_exclusive(v___x_926_)) as u8;
                        if v_isSharedCheck_984_ == 0 {
                            v___x_929_ = v___x_926_;
                            v_isShared_930_ = v_isSharedCheck_984_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_927_);
                            lean_dec(v___x_926_);
                            v___x_929_ = lean_box(0);
                            v_isShared_930_ = v_isSharedCheck_984_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_924_);
                        lean_dec_ref(v_rhsExpr_912_);
                        lean_dec_ref(v_lhsExpr_911_);
                        lean_dec_ref(v_discrExpr_909_);
                        lean_dec_ref(v_rhs_908_);
                        lean_dec_ref(v_discr_906_);
                        v_a_985_ = lean_ctor_get(v___x_926_, 0);
                        v_isSharedCheck_992_ = (!lean_is_exclusive(v___x_926_)) as u8;
                        if v_isSharedCheck_992_ == 0 {
                            v___x_987_ = v___x_926_;
                            v_isShared_988_ = v_isSharedCheck_992_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_985_);
                            lean_dec(v___x_926_);
                            v___x_987_ = lean_box(0);
                            v_isShared_988_ = v_isSharedCheck_992_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhsExpr_912_);
                    lean_dec_ref(v_lhsExpr_911_);
                    lean_dec_ref(v_atomExpr_910_);
                    lean_dec_ref(v_discrExpr_909_);
                    lean_dec_ref(v_rhs_908_);
                    lean_dec_ref(v_atom_907_);
                    lean_dec_ref(v_discr_906_);
                    v_a_993_ = lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_1000_ = (!lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_1000_ == 0 {
                        v___x_995_ = v___x_923_;
                        v_isShared_996_ = v_isSharedCheck_1000_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_993_);
                        lean_dec(v___x_923_);
                        v___x_995_ = lean_box(0);
                        v_isShared_996_ = v_isSharedCheck_1000_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_927_) == 1 {
                    lean_del_object(v___x_929_);
                    v_val_931_ = lean_ctor_get(v_a_927_, 0);
                    v_isSharedCheck_979_ = (!lean_is_exclusive(v_a_927_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v___x_933_ = v_a_927_;
                        v_isShared_934_ = v_isSharedCheck_979_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_931_);
                        lean_dec(v_a_927_);
                        v___x_933_ = lean_box(0);
                        v_isShared_934_ = v_isSharedCheck_979_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_927_);
                    lean_dec(v_a_924_);
                    lean_dec_ref(v_rhsExpr_912_);
                    lean_dec_ref(v_lhsExpr_911_);
                    lean_dec_ref(v_discrExpr_909_);
                    lean_dec_ref(v_rhs_908_);
                    lean_dec_ref(v_discr_906_);
                    v___x_980_ = lean_box(0);
                    if v_isShared_930_ == 0 {
                        lean_ctor_set(v___x_929_, 0, v___x_980_);
                        v___x_982_ = v___x_929_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
                        v___x_982_ = v_reuseFailAlloc_983_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_935_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_931_);
                if lean_obj_tag(v___x_935_) == 0 {
                    v_a_936_ = lean_ctor_get(v___x_935_, 0);
                    lean_inc(v_a_936_);
                    lean_dec_ref_known(v___x_935_, 1);
                    v___x_937_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0;
                    v___x_938_ = lean_box(0);
                    v___x_939_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
                    lean_inc(v_a_924_);
                    lean_inc_ref_n(v_discrExpr_909_, 2);
                    v___x_940_ = l_Lean_mkAppB(v___x_939_, v_discrExpr_909_, v_a_924_);
                    v___x_941_ = 3;
                    lean_inc_ref(v___x_940_);
                    v___x_942_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
                        v_discr_906_,
                        v_a_936_,
                        v_discrExpr_909_,
                        v_a_924_,
                        v___x_941_,
                        v___x_940_,
                    );
                    if lean_obj_tag(v___x_942_) == 0 {
                        v_a_943_ = lean_ctor_get(v___x_942_, 0);
                        v_isSharedCheck_962_ = (!lean_is_exclusive(v___x_942_)) as u8;
                        if v_isSharedCheck_962_ == 0 {
                            v___x_945_ = v___x_942_;
                            v_isShared_946_ = v_isSharedCheck_962_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_943_);
                            lean_dec(v___x_942_);
                            v___x_945_ = lean_box(0);
                            v_isShared_946_ = v_isSharedCheck_962_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_940_);
                        lean_del_object(v___x_933_);
                        lean_dec_ref(v_rhsExpr_912_);
                        lean_dec_ref(v_lhsExpr_911_);
                        lean_dec_ref(v_discrExpr_909_);
                        lean_dec_ref(v_rhs_908_);
                        v_a_963_ = lean_ctor_get(v___x_942_, 0);
                        v_isSharedCheck_970_ = (!lean_is_exclusive(v___x_942_)) as u8;
                        if v_isSharedCheck_970_ == 0 {
                            v___x_965_ = v___x_942_;
                            v_isShared_966_ = v_isSharedCheck_970_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_963_);
                            lean_dec(v___x_942_);
                            v___x_965_ = lean_box(0);
                            v_isShared_966_ = v_isSharedCheck_970_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_933_);
                    lean_dec(v_a_924_);
                    lean_dec_ref(v_rhsExpr_912_);
                    lean_dec_ref(v_lhsExpr_911_);
                    lean_dec_ref(v_discrExpr_909_);
                    lean_dec_ref(v_rhs_908_);
                    lean_dec_ref(v_discr_906_);
                    v_a_971_ = lean_ctor_get(v___x_935_, 0);
                    v_isSharedCheck_978_ = (!lean_is_exclusive(v___x_935_)) as u8;
                    if v_isSharedCheck_978_ == 0 {
                        v___x_973_ = v___x_935_;
                        v_isShared_974_ = v_isSharedCheck_978_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_971_);
                        lean_dec(v___x_935_);
                        v___x_973_ = lean_box(0);
                        v_isShared_974_ = v_isSharedCheck_978_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_bvExpr_947_ = lean_ctor_get(v_a_943_, 0);
                lean_inc_ref(v_bvExpr_947_);
                v_expr_948_ = lean_ctor_get(v_a_943_, 3);
                lean_inc_ref_n(v_expr_948_, 2);
                v___x_949_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10;
                v___x_950_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11;
                v___x_951_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12;
                v___x_952_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13;
                v_lemmaName_953_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1;
                v___f_954_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed as *mut core::ffi::c_void, 20, 14);
                lean_closure_set(v___f_954_, 0, v_expr_948_);
                lean_closure_set(v___f_954_, 1, v_a_943_);
                lean_closure_set(v___f_954_, 2, v_rhs_908_);
                lean_closure_set(v___f_954_, 3, v_lemmaName_953_);
                lean_closure_set(v___f_954_, 4, v___x_938_);
                lean_closure_set(v___f_954_, 5, v_discrExpr_909_);
                lean_closure_set(v___f_954_, 6, v_lhsExpr_911_);
                lean_closure_set(v___f_954_, 7, v_rhsExpr_912_);
                lean_closure_set(v___f_954_, 8, v___x_949_);
                lean_closure_set(v___f_954_, 9, v___x_950_);
                lean_closure_set(v___f_954_, 10, v___x_951_);
                lean_closure_set(v___f_954_, 11, v___x_952_);
                lean_closure_set(v___f_954_, 12, v___x_937_);
                lean_closure_set(v___f_954_, 13, v___x_940_);
                v___x_955_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_955_, 0, v_bvExpr_947_);
                lean_ctor_set(v___x_955_, 1, v___f_954_);
                lean_ctor_set(v___x_955_, 2, v_expr_948_);
                if v_isShared_934_ == 0 {
                    lean_ctor_set(v___x_933_, 0, v___x_955_);
                    v___x_957_ = v___x_933_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_955_);
                    v___x_957_ = v_reuseFailAlloc_961_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_946_ == 0 {
                    lean_ctor_set(v___x_945_, 0, v___x_957_);
                    v___x_959_ = v___x_945_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
                    v___x_959_ = v_reuseFailAlloc_960_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_959_;
            }
            6 => {
                if v_isShared_966_ == 0 {
                    v___x_968_ = v___x_965_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
                    v___x_968_ = v_reuseFailAlloc_969_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_968_;
            }
            8 => {
                if v_isShared_974_ == 0 {
                    v___x_976_ = v___x_973_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
                    v___x_976_ = v_reuseFailAlloc_977_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_976_;
            }
            10 => {
                return v___x_982_;
            }
            11 => {
                if v_isShared_988_ == 0 {
                    v___x_990_ = v___x_987_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
                    v___x_990_ = v_reuseFailAlloc_991_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_990_;
            }
            13 => {
                if v_isShared_996_ == 0 {
                    v___x_998_ = v___x_995_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
                    v___x_998_ = v_reuseFailAlloc_999_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___boxed(
    mut v_discr_1001_: *mut LeanObject,
    mut v_atom_1002_: *mut LeanObject,
    mut v_rhs_1003_: *mut LeanObject,
    mut v_discrExpr_1004_: *mut LeanObject,
    mut v_atomExpr_1005_: *mut LeanObject,
    mut v_lhsExpr_1006_: *mut LeanObject,
    mut v_rhsExpr_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_1001_, v_atom_1002_, v_rhs_1003_, v_discrExpr_1004_, v_atomExpr_1005_, v_lhsExpr_1006_, v_rhsExpr_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
    lean_dec(v_a_1011_);
    lean_dec_ref(v_a_1010_);
    lean_dec(v_a_1009_);
    lean_dec_ref(v_a_1008_);
    return v_res_1013_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(
    mut v_discr_1014_: *mut LeanObject,
    mut v_atom_1015_: *mut LeanObject,
    mut v_rhs_1016_: *mut LeanObject,
    mut v_discrExpr_1017_: *mut LeanObject,
    mut v_atomExpr_1018_: *mut LeanObject,
    mut v_lhsExpr_1019_: *mut LeanObject,
    mut v_rhsExpr_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1027_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_1014_, v_atom_1015_, v_rhs_1016_, v_discrExpr_1017_, v_atomExpr_1018_, v_lhsExpr_1019_, v_rhsExpr_1020_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
    return v___x_1027_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___boxed(
    mut v_discr_1028_: *mut LeanObject,
    mut v_atom_1029_: *mut LeanObject,
    mut v_rhs_1030_: *mut LeanObject,
    mut v_discrExpr_1031_: *mut LeanObject,
    mut v_atomExpr_1032_: *mut LeanObject,
    mut v_lhsExpr_1033_: *mut LeanObject,
    mut v_rhsExpr_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1041_: *mut LeanObject = core::ptr::null_mut();
    v_res_1041_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(v_discr_1028_, v_atom_1029_, v_rhs_1030_, v_discrExpr_1031_, v_atomExpr_1032_, v_lhsExpr_1033_, v_rhsExpr_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
    lean_dec(v_a_1039_);
    lean_dec_ref(v_a_1038_);
    lean_dec(v_a_1037_);
    lean_dec_ref(v_a_1036_);
    lean_dec(v_a_1035_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(
    mut v_discr_1042_: *mut LeanObject,
    mut v_atom_1043_: *mut LeanObject,
    mut v_lhs_1044_: *mut LeanObject,
    mut v_rhs_1045_: *mut LeanObject,
    mut v_discrExpr_1046_: *mut LeanObject,
    mut v_atomExpr_1047_: *mut LeanObject,
    mut v_lhsExpr_1048_: *mut LeanObject,
    mut v_rhsExpr_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_a_1053_: *mut LeanObject,
    mut v_a_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v_val_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1067_: u8 = 0;
    let mut v_val_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1074_: u8 = 0;
    let mut v_a_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1082_: u8 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_a_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_rhsExpr_1049_);
                lean_inc_ref(v_lhsExpr_1048_);
                lean_inc_ref(v_atomExpr_1047_);
                lean_inc_ref(v_discrExpr_1046_);
                lean_inc_ref(v_atom_1043_);
                lean_inc_ref(v_discr_1042_);
                v___x_1056_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_1042_, v_atom_1043_, v_lhs_1044_, v_discrExpr_1046_, v_atomExpr_1047_, v_lhsExpr_1048_, v_rhsExpr_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
                if lean_obj_tag(v___x_1056_) == 0 {
                    v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
                    v_isSharedCheck_1087_ = (!lean_is_exclusive(v___x_1056_)) as u8;
                    if v_isSharedCheck_1087_ == 0 {
                        v___x_1059_ = v___x_1056_;
                        v_isShared_1060_ = v_isSharedCheck_1087_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1057_);
                        lean_dec(v___x_1056_);
                        v___x_1059_ = lean_box(0);
                        v_isShared_1060_ = v_isSharedCheck_1087_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_rhsExpr_1049_);
                    lean_dec_ref(v_lhsExpr_1048_);
                    lean_dec_ref(v_atomExpr_1047_);
                    lean_dec_ref(v_discrExpr_1046_);
                    lean_dec_ref(v_rhs_1045_);
                    lean_dec_ref(v_atom_1043_);
                    lean_dec_ref(v_discr_1042_);
                    v_a_1088_ = lean_ctor_get(v___x_1056_, 0);
                    v_isSharedCheck_1095_ = (!lean_is_exclusive(v___x_1056_)) as u8;
                    if v_isSharedCheck_1095_ == 0 {
                        v___x_1090_ = v___x_1056_;
                        v_isShared_1091_ = v_isSharedCheck_1095_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1088_);
                        lean_dec(v___x_1056_);
                        v___x_1090_ = lean_box(0);
                        v_isShared_1091_ = v_isSharedCheck_1095_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1057_) == 1 {
                    lean_del_object(v___x_1059_);
                    v_val_1061_ = lean_ctor_get(v_a_1057_, 0);
                    lean_inc(v_val_1061_);
                    lean_dec_ref_known(v_a_1057_, 1);
                    v___x_1062_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(
                        v_val_1061_,
                        v_a_1050_,
                    );
                    if lean_obj_tag(v___x_1062_) == 0 {
                        lean_dec_ref_known(v___x_1062_, 1);
                        v___x_1063_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_1042_, v_atom_1043_, v_rhs_1045_, v_discrExpr_1046_, v_atomExpr_1047_, v_lhsExpr_1048_, v_rhsExpr_1049_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
                        if lean_obj_tag(v___x_1063_) == 0 {
                            v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
                            v_isSharedCheck_1074_ = (!lean_is_exclusive(v___x_1063_)) as u8;
                            if v_isSharedCheck_1074_ == 0 {
                                v___x_1066_ = v___x_1063_;
                                v_isShared_1067_ = v_isSharedCheck_1074_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1064_);
                                lean_dec(v___x_1063_);
                                v___x_1066_ = lean_box(0);
                                v_isShared_1067_ = v_isSharedCheck_1074_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1075_ = lean_ctor_get(v___x_1063_, 0);
                            v_isSharedCheck_1082_ = (!lean_is_exclusive(v___x_1063_)) as u8;
                            if v_isSharedCheck_1082_ == 0 {
                                v___x_1077_ = v___x_1063_;
                                v_isShared_1078_ = v_isSharedCheck_1082_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1075_);
                                lean_dec(v___x_1063_);
                                v___x_1077_ = lean_box(0);
                                v_isShared_1078_ = v_isSharedCheck_1082_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_rhsExpr_1049_);
                        lean_dec_ref(v_lhsExpr_1048_);
                        lean_dec_ref(v_atomExpr_1047_);
                        lean_dec_ref(v_discrExpr_1046_);
                        lean_dec_ref(v_rhs_1045_);
                        lean_dec_ref(v_atom_1043_);
                        lean_dec_ref(v_discr_1042_);
                        return v___x_1062_;
                    }
                } else {
                    lean_dec(v_a_1057_);
                    lean_dec_ref(v_rhsExpr_1049_);
                    lean_dec_ref(v_lhsExpr_1048_);
                    lean_dec_ref(v_atomExpr_1047_);
                    lean_dec_ref(v_discrExpr_1046_);
                    lean_dec_ref(v_rhs_1045_);
                    lean_dec_ref(v_atom_1043_);
                    lean_dec_ref(v_discr_1042_);
                    v___x_1083_ = lean_box(0);
                    if v_isShared_1060_ == 0 {
                        lean_ctor_set(v___x_1059_, 0, v___x_1083_);
                        v___x_1085_ = v___x_1059_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
                        v___x_1085_ = v_reuseFailAlloc_1086_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1064_) == 1 {
                    lean_del_object(v___x_1066_);
                    v_val_1068_ = lean_ctor_get(v_a_1064_, 0);
                    lean_inc(v_val_1068_);
                    lean_dec_ref_known(v_a_1064_, 1);
                    v___x_1069_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(
                        v_val_1068_,
                        v_a_1050_,
                    );
                    return v___x_1069_;
                } else {
                    lean_dec(v_a_1064_);
                    v___x_1070_ = lean_box(0);
                    if v_isShared_1067_ == 0 {
                        lean_ctor_set(v___x_1066_, 0, v___x_1070_);
                        v___x_1072_ = v___x_1066_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
                        v___x_1072_ = v_reuseFailAlloc_1073_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1072_;
            }
            4 => {
                if v_isShared_1078_ == 0 {
                    v___x_1080_ = v___x_1077_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
                    v___x_1080_ = v_reuseFailAlloc_1081_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1080_;
            }
            6 => {
                return v___x_1085_;
            }
            7 => {
                if v_isShared_1091_ == 0 {
                    v___x_1093_ = v___x_1090_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg___boxed(
    mut v_discr_1096_: *mut LeanObject,
    mut v_atom_1097_: *mut LeanObject,
    mut v_lhs_1098_: *mut LeanObject,
    mut v_rhs_1099_: *mut LeanObject,
    mut v_discrExpr_1100_: *mut LeanObject,
    mut v_atomExpr_1101_: *mut LeanObject,
    mut v_lhsExpr_1102_: *mut LeanObject,
    mut v_rhsExpr_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v_a_1106_: *mut LeanObject,
    mut v_a_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
    mut v_a_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(
        v_discr_1096_,
        v_atom_1097_,
        v_lhs_1098_,
        v_rhs_1099_,
        v_discrExpr_1100_,
        v_atomExpr_1101_,
        v_lhsExpr_1102_,
        v_rhsExpr_1103_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
        v_a_1108_,
    );
    lean_dec(v_a_1108_);
    lean_dec_ref(v_a_1107_);
    lean_dec(v_a_1106_);
    lean_dec_ref(v_a_1105_);
    lean_dec(v_a_1104_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_addCondLemmas(
    mut v_discr_1111_: *mut LeanObject,
    mut v_atom_1112_: *mut LeanObject,
    mut v_lhs_1113_: *mut LeanObject,
    mut v_rhs_1114_: *mut LeanObject,
    mut v_discrExpr_1115_: *mut LeanObject,
    mut v_atomExpr_1116_: *mut LeanObject,
    mut v_lhsExpr_1117_: *mut LeanObject,
    mut v_rhsExpr_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(
        v_discr_1111_,
        v_atom_1112_,
        v_lhs_1113_,
        v_rhs_1114_,
        v_discrExpr_1115_,
        v_atomExpr_1116_,
        v_lhsExpr_1117_,
        v_rhsExpr_1118_,
        v_a_1119_,
        v_a_1121_,
        v_a_1122_,
        v_a_1123_,
        v_a_1124_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_addCondLemmas___boxed(
    mut v_discr_1127_: *mut LeanObject,
    mut v_atom_1128_: *mut LeanObject,
    mut v_lhs_1129_: *mut LeanObject,
    mut v_rhs_1130_: *mut LeanObject,
    mut v_discrExpr_1131_: *mut LeanObject,
    mut v_atomExpr_1132_: *mut LeanObject,
    mut v_lhsExpr_1133_: *mut LeanObject,
    mut v_rhsExpr_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
    mut v_a_1138_: *mut LeanObject,
    mut v_a_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
    mut v_a_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1142_: *mut LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas(
        v_discr_1127_,
        v_atom_1128_,
        v_lhs_1129_,
        v_rhs_1130_,
        v_discrExpr_1131_,
        v_atomExpr_1132_,
        v_lhsExpr_1133_,
        v_rhsExpr_1134_,
        v_a_1135_,
        v_a_1136_,
        v_a_1137_,
        v_a_1138_,
        v_a_1139_,
        v_a_1140_,
    );
    lean_dec(v_a_1140_);
    lean_dec_ref(v_a_1139_);
    lean_dec(v_a_1138_);
    lean_dec_ref(v_a_1137_);
    lean_dec(v_a_1136_);
    lean_dec(v_a_1135_);
    return v_res_1142_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
}
