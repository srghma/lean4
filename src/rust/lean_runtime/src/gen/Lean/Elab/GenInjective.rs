// Lean compiler output
// Module: Lean.Elab.GenInjective
// Imports: Lean.Elab.Command Lean.Meta.Injective Lean.Meta.Constructions.CtorIdx
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg,
};
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdx,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::Injective::{
    initialize_Lean_Meta_Injective, l_Lean_Meta_mkInjectiveTheorems,
    runtime_initialize_Lean_Meta_Injective,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [103, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value) as *mut LeanObject,13979199899680194611 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [71, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value) as *mut LeanObject,1831590326038283434 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,15766973221561412779 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut LeanObject,8926060025602177174 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut LeanObject,2160535094612547780 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut LeanObject,310123643824003617 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 71, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value) as *mut LeanObject,9854580972373139301 as *mut LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(
    mut v___x_94_: *mut LeanObject,
    mut v___x_95_: *mut LeanObject,
    mut v___y_96_: *mut LeanObject,
    mut v___y_97_: *mut LeanObject,
    mut v___y_98_: *mut LeanObject,
    mut v___y_99_: *mut LeanObject,
    mut v___y_100_: *mut LeanObject,
    mut v___y_101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_110_: u8 = 0;
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_103_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                    v___x_94_, v___x_95_, v___y_100_, v___y_101_,
                );
                if lean_obj_tag(v___x_103_) == 0 {
                    v_a_104_ = lean_ctor_get(v___x_103_, 0);
                    lean_inc_n(v_a_104_, 2);
                    lean_dec_ref_known(v___x_103_, 1);
                    v___x_105_ =
                        l_mkCtorIdx(v_a_104_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
                    if lean_obj_tag(v___x_105_) == 0 {
                        lean_dec_ref_known(v___x_105_, 1);
                        v___x_106_ = l_Lean_Meta_mkInjectiveTheorems(
                            v_a_104_, v___y_98_, v___y_99_, v___y_100_, v___y_101_,
                        );
                        return v___x_106_;
                    } else {
                        lean_dec(v_a_104_);
                        return v___x_105_;
                    }
                } else {
                    v_a_107_ = lean_ctor_get(v___x_103_, 0);
                    v_isSharedCheck_114_ = (!lean_is_exclusive(v___x_103_)) as u8;
                    if v_isSharedCheck_114_ == 0 {
                        v___x_109_ = v___x_103_;
                        v_isShared_110_ = v_isSharedCheck_114_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_107_);
                        lean_dec(v___x_103_);
                        v___x_109_ = lean_box(0);
                        v_isShared_110_ = v_isSharedCheck_114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_110_ == 0 {
                    v___x_112_ = v___x_109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
                    v___x_112_ = v_reuseFailAlloc_113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(
    mut v___x_115_: *mut LeanObject,
    mut v___x_116_: *mut LeanObject,
    mut v___y_117_: *mut LeanObject,
    mut v___y_118_: *mut LeanObject,
    mut v___y_119_: *mut LeanObject,
    mut v___y_120_: *mut LeanObject,
    mut v___y_121_: *mut LeanObject,
    mut v___y_122_: *mut LeanObject,
    mut v___y_123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_124_ =
        l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(
            v___x_115_, v___x_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_,
            v___y_122_,
        );
    lean_dec(v___y_122_);
    lean_dec_ref(v___y_121_);
    lean_dec(v___y_120_);
    lean_dec_ref(v___y_119_);
    lean_dec(v___y_118_);
    lean_dec_ref(v___y_117_);
    return v_res_124_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(
    mut v_stx_125_: *mut LeanObject,
    mut v_a_126_: *mut LeanObject,
    mut v_a_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    v___x_129_ = lean_unsigned_to_nat(1);
    v___x_130_ = l_Lean_Syntax_getArg(v_stx_125_, v___x_129_);
    v___x_131_ = lean_box(0);
    v___f_132_ = lean_alloc_closure(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    lean_closure_set(v___f_132_, 0, v___x_130_);
    lean_closure_set(v___f_132_, 1, v___x_131_);
    v___x_133_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_132_, v_a_126_, v_a_127_);
    return v___x_133_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed(
    mut v_stx_134_: *mut LeanObject,
    mut v_a_135_: *mut LeanObject,
    mut v_a_136_: *mut LeanObject,
    mut v_a_137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_138_: *mut LeanObject = core::ptr::null_mut();
    v_res_138_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(
        v_stx_134_, v_a_135_, v_a_136_,
    );
    lean_dec(v_a_136_);
    lean_dec_ref(v_a_135_);
    lean_dec(v_stx_134_);
    return v_res_138_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1()
-> *mut LeanObject {
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    v___x_180_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_181_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4;
    v___x_182_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17;
    v___x_183_ = lean_alloc_closure(
        l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_184_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_180_, v___x_181_, v___x_182_, v___x_183_,
    );
    return v___x_184_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(
    mut v_a_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_186_: *mut LeanObject = core::ptr::null_mut();
    v_res_186_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
    return v_res_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_GenInjective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_GenInjective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_GenInjective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_GenInjective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_GenInjective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_GenInjective(builtin);
}
