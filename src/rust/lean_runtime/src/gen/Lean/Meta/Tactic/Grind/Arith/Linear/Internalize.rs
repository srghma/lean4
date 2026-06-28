// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Internalize
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule Lean.Meta.Tactic.Grind.Arith.Util Lean.Meta.Tactic.Grind.Arith.Linear.StructId Lean.Meta.Tactic.Grind.Arith.Linear.Var Lean.Meta.Tactic.Grind.Arith.Linear.Util Lean.Meta.Tactic.Grind.Arith.Linear.Reify
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::OfNatModule::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule,
    l_Lean_Meta_Grind_Arith_Linear_ofNatModule,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify, l_Lean_Meta_Grind_Arith_Linear_isAddInst,
    l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst, l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst,
    l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst, l_Lean_Meta_Grind_Arith_Linear_isSubInst,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::StructId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
    l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f,
    l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::l_Lean_Meta_Grind_Arith_Linear_linearExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
    l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var, l_Lean_Meta_Grind_Arith_Linear_mkVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util, l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent,
    l_Lean_Meta_Grind_Arith_isNatNum, runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getConfig___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [79, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__0_value) as *mut LeanObject,1389984430658442515 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__1_value) as *mut LeanObject,9294582609080780319 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__3_value) as *mut LeanObject,18263865437487147968 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__4_value) as *mut LeanObject,2651253468108498348 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__6_value) as *mut LeanObject,4977321555018234431 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__7_value) as *mut LeanObject,4463466624472370110 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__9_value) as *mut LeanObject,5779414593499529281 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__10_value) as *mut LeanObject,7063772860359172143 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__12_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__13_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__15_value) as *mut LeanObject,9626815015619986526 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__16_value) as *mut LeanObject,17185717442815859305 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__18_value) as *mut LeanObject,15703084674812832738 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__19_value) as *mut LeanObject,13609749952674037527 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__21_value) as *mut LeanObject,2929883540436775422 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__22_value) as *mut LeanObject,1611444129324655608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__24_value) as *mut LeanObject,16856108565602861689 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__25_value) as *mut LeanObject,4187025665268973031 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__27_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__28_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__0_value) as *mut LeanObject,8347582161988589016 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__1_value) as *mut LeanObject,7316284823769321069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__3_value) as *mut LeanObject,17878876274162330439 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__4_value) as *mut LeanObject,11833570877100518198 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__6_value) as *mut LeanObject,13744984671752750173 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__7_value) as *mut LeanObject,9682224670061807480 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__9_value) as *mut LeanObject,11858238400308895562 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__10_value) as *mut LeanObject,6100819061652633370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_0: LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__1_value)
                as *mut LeanObject,
            10740975855909177240 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__2_value)
                as *mut LeanObject,
            15515019119152942329 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_value: LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__4_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [32, 61, 61, 62, 32, 0],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(
    mut v_e_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    v___x_851_ = l_Lean_Expr_cleanupAnnotations(v_e_850_);
    v___x_852_ = l_Lean_Expr_isApp(v___x_851_);
    if v___x_852_ == 0 {
        let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_851_);
        v___x_853_ = lean_box(0);
        return v___x_853_;
    } else {
        let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_855_: u8 = 0;
        v___x_854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_851_);
        v___x_855_ = l_Lean_Expr_isApp(v___x_854_);
        if v___x_855_ == 0 {
            let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_854_);
            v___x_856_ = lean_box(0);
            return v___x_856_;
        } else {
            let mut v_arg_857_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_860_: u8 = 0;
            v_arg_857_ = lean_ctor_get(v___x_854_, 1);
            lean_inc_ref(v_arg_857_);
            v___x_858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_854_);
            v___x_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__2;
            v___x_860_ = l_Lean_Expr_isConstOf(v___x_858_, v___x_859_);
            if v___x_860_ == 0 {
                let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_862_: u8 = 0;
                v___x_861_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5;
                v___x_862_ = l_Lean_Expr_isConstOf(v___x_858_, v___x_861_);
                if v___x_862_ == 0 {
                    let mut v___x_863_: u8 = 0;
                    lean_dec_ref(v_arg_857_);
                    v___x_863_ = l_Lean_Expr_isApp(v___x_858_);
                    if v___x_863_ == 0 {
                        let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref(v___x_858_);
                        v___x_864_ = lean_box(0);
                        return v___x_864_;
                    } else {
                        let mut v_arg_865_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_868_: u8 = 0;
                        v_arg_865_ = lean_ctor_get(v___x_858_, 1);
                        lean_inc_ref(v_arg_865_);
                        v___x_866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_858_);
                        v___x_867_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__8;
                        v___x_868_ = l_Lean_Expr_isConstOf(v___x_866_, v___x_867_);
                        if v___x_868_ == 0 {
                            let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_870_: u8 = 0;
                            v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__11;
                            v___x_870_ = l_Lean_Expr_isConstOf(v___x_866_, v___x_869_);
                            if v___x_870_ == 0 {
                                let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_872_: u8 = 0;
                                v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14;
                                v___x_872_ = l_Lean_Expr_isConstOf(v___x_866_, v___x_871_);
                                if v___x_872_ == 0 {
                                    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_874_: u8 = 0;
                                    v___x_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17;
                                    v___x_874_ = l_Lean_Expr_isConstOf(v___x_866_, v___x_873_);
                                    if v___x_874_ == 0 {
                                        let mut v___x_875_: u8 = 0;
                                        lean_dec_ref(v_arg_865_);
                                        v___x_875_ = l_Lean_Expr_isApp(v___x_866_);
                                        if v___x_875_ == 0 {
                                            let mut v___x_876_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            lean_dec_ref(v___x_866_);
                                            v___x_876_ = lean_box(0);
                                            return v___x_876_;
                                        } else {
                                            let mut v_arg_877_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_878_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_879_: u8 = 0;
                                            v_arg_877_ = lean_ctor_get(v___x_866_, 1);
                                            lean_inc_ref(v_arg_877_);
                                            v___x_878_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_866_);
                                            v___x_879_ = l_Lean_Expr_isApp(v___x_878_);
                                            if v___x_879_ == 0 {
                                                let mut v___x_880_: *mut LeanObject =
                                                    core::ptr::null_mut();
                                                lean_dec_ref(v___x_878_);
                                                lean_dec_ref(v_arg_877_);
                                                v___x_880_ = lean_box(0);
                                                return v___x_880_;
                                            } else {
                                                let mut v___x_881_: *mut LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_882_: u8 = 0;
                                                v___x_881_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_878_);
                                                v___x_882_ = l_Lean_Expr_isApp(v___x_881_);
                                                if v___x_882_ == 0 {
                                                    let mut v___x_883_: *mut LeanObject =
                                                        core::ptr::null_mut();
                                                    lean_dec_ref(v___x_881_);
                                                    lean_dec_ref(v_arg_877_);
                                                    v___x_883_ = lean_box(0);
                                                    return v___x_883_;
                                                } else {
                                                    let mut v___x_884_: *mut LeanObject =
                                                        core::ptr::null_mut();
                                                    let mut v___x_885_: *mut LeanObject =
                                                        core::ptr::null_mut();
                                                    let mut v___x_886_: u8 = 0;
                                                    v___x_884_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_881_,
                                                    );
                                                    v___x_885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20;
                                                    v___x_886_ = l_Lean_Expr_isConstOf(
                                                        v___x_884_, v___x_885_,
                                                    );
                                                    if v___x_886_ == 0 {
                                                        let mut v___x_887_: *mut LeanObject =
                                                            core::ptr::null_mut();
                                                        let mut v___x_888_: u8 = 0;
                                                        v___x_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23;
                                                        v___x_888_ = l_Lean_Expr_isConstOf(
                                                            v___x_884_, v___x_887_,
                                                        );
                                                        if v___x_888_ == 0 {
                                                            let mut v___x_889_: *mut LeanObject =
                                                                core::ptr::null_mut();
                                                            let mut v___x_890_: u8 = 0;
                                                            v___x_889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26;
                                                            v___x_890_ = l_Lean_Expr_isConstOf(
                                                                v___x_884_, v___x_889_,
                                                            );
                                                            if v___x_890_ == 0 {
                                                                let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
                                                                let mut v___x_892_: u8 = 0;
                                                                v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29;
                                                                v___x_892_ = l_Lean_Expr_isConstOf(
                                                                    v___x_884_, v___x_891_,
                                                                );
                                                                lean_dec_ref(v___x_884_);
                                                                if v___x_892_ == 0 {
                                                                    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
                                                                    lean_dec_ref(v_arg_877_);
                                                                    v___x_893_ = lean_box(0);
                                                                    return v___x_893_;
                                                                } else {
                                                                    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
                                                                    v___x_894_ = lean_alloc_ctor(
                                                                        1,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                    lean_ctor_set(
                                                                        v___x_894_, 0, v_arg_877_,
                                                                    );
                                                                    return v___x_894_;
                                                                }
                                                            } else {
                                                                let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
                                                                lean_dec_ref(v___x_884_);
                                                                v___x_895_ = lean_alloc_ctor(
                                                                    1,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_895_, 0, v_arg_877_,
                                                                );
                                                                return v___x_895_;
                                                            }
                                                        } else {
                                                            let mut v___x_896_: *mut LeanObject =
                                                                core::ptr::null_mut();
                                                            lean_dec_ref(v___x_884_);
                                                            v___x_896_ =
                                                                lean_alloc_ctor(1, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_896_, 0, v_arg_877_,
                                                            );
                                                            return v___x_896_;
                                                        }
                                                    } else {
                                                        let mut v___x_897_: *mut LeanObject =
                                                            core::ptr::null_mut();
                                                        lean_dec_ref(v___x_884_);
                                                        v___x_897_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_897_, 0, v_arg_877_);
                                                        return v___x_897_;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
                                        lean_dec_ref(v___x_866_);
                                        v___x_898_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_898_, 0, v_arg_865_);
                                        return v___x_898_;
                                    }
                                } else {
                                    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec_ref(v___x_866_);
                                    v___x_899_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_899_, 0, v_arg_865_);
                                    return v___x_899_;
                                }
                            } else {
                                let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec_ref(v___x_866_);
                                v___x_900_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_900_, 0, v_arg_865_);
                                return v___x_900_;
                            }
                        } else {
                            let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref(v___x_866_);
                            v___x_901_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_901_, 0, v_arg_865_);
                            return v___x_901_;
                        }
                    }
                } else {
                    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v___x_858_);
                    v___x_902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_902_, 0, v_arg_857_);
                    return v___x_902_;
                }
            } else {
                let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_858_);
                v___x_903_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_903_, 0, v_arg_857_);
                return v___x_903_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(
    mut v_parent_x3f_924_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_parent_x3f_924_) == 1 {
        let mut v_val_925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        v_val_925_ = lean_ctor_get(v_parent_x3f_924_, 0);
        lean_inc_n(v_val_925_, 2);
        lean_dec_ref_known(v_parent_x3f_924_, 1);
        v___x_926_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_val_925_);
        if lean_obj_tag(v___x_926_) == 0 {
            let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_928_: u8 = 0;
            v___x_927_ = l_Lean_Expr_cleanupAnnotations(v_val_925_);
            v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
            if v___x_928_ == 0 {
                lean_dec_ref(v___x_927_);
                return v___x_928_;
            } else {
                let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_930_: u8 = 0;
                v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
                v___x_930_ = l_Lean_Expr_isApp(v___x_929_);
                if v___x_930_ == 0 {
                    lean_dec_ref(v___x_929_);
                    return v___x_930_;
                } else {
                    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_932_: u8 = 0;
                    v___x_931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_929_);
                    v___x_932_ = l_Lean_Expr_isApp(v___x_931_);
                    if v___x_932_ == 0 {
                        lean_dec_ref(v___x_931_);
                        return v___x_932_;
                    } else {
                        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_934_: u8 = 0;
                        v___x_933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_931_);
                        v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
                        if v___x_934_ == 0 {
                            lean_dec_ref(v___x_933_);
                            return v___x_934_;
                        } else {
                            let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_937_: u8 = 0;
                            v___x_935_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
                            v___x_936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__2;
                            v___x_937_ = l_Lean_Expr_isConstOf(v___x_935_, v___x_936_);
                            if v___x_937_ == 0 {
                                let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_939_: u8 = 0;
                                v___x_938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__5;
                                v___x_939_ = l_Lean_Expr_isConstOf(v___x_935_, v___x_938_);
                                if v___x_939_ == 0 {
                                    let mut v___x_940_: u8 = 0;
                                    v___x_940_ = l_Lean_Expr_isApp(v___x_935_);
                                    if v___x_940_ == 0 {
                                        lean_dec_ref(v___x_935_);
                                        return v___x_940_;
                                    } else {
                                        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_942_: u8 = 0;
                                        v___x_941_ = l_Lean_Expr_appFnCleanup___redArg(v___x_935_);
                                        v___x_942_ = l_Lean_Expr_isApp(v___x_941_);
                                        if v___x_942_ == 0 {
                                            lean_dec_ref(v___x_941_);
                                            return v___x_942_;
                                        } else {
                                            let mut v___x_943_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_944_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_945_: u8 = 0;
                                            v___x_943_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_941_);
                                            v___x_944_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__8;
                                            v___x_945_ =
                                                l_Lean_Expr_isConstOf(v___x_943_, v___x_944_);
                                            if v___x_945_ == 0 {
                                                let mut v___x_946_: *mut LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_947_: u8 = 0;
                                                v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___closed__11;
                                                v___x_947_ =
                                                    l_Lean_Expr_isConstOf(v___x_943_, v___x_946_);
                                                lean_dec_ref(v___x_943_);
                                                if v___x_947_ == 0 {
                                                    return v___x_947_;
                                                } else {
                                                    return v___x_934_;
                                                }
                                            } else {
                                                lean_dec_ref(v___x_943_);
                                                return v___x_934_;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_935_);
                                    return v___x_934_;
                                }
                            } else {
                                lean_dec_ref(v___x_935_);
                                return v___x_934_;
                            }
                        }
                    }
                }
            }
        } else {
            let mut v___x_948_: u8 = 0;
            lean_dec_ref_known(v___x_926_, 1);
            lean_dec(v_val_925_);
            v___x_948_ = 1;
            return v___x_948_;
        }
    } else {
        let mut v___x_949_: u8 = 0;
        lean_dec(v_parent_x3f_924_);
        v___x_949_ = 1;
        return v___x_949_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent___boxed(
    mut v_parent_x3f_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_951_: u8 = 0;
    let mut v_r_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_950_);
    v_r_952_ = lean_box((v_res_951_) as usize);
    return v_r_952_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(
    mut v_e_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
    mut v_a_957_: *mut LeanObject,
    mut v_a_958_: *mut LeanObject,
    mut v_a_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
    mut v_a_961_: *mut LeanObject,
    mut v_a_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
    mut v_a_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_970_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_975_: u8 = 0;
    let mut v_unused_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_966_ = 1;
                v___x_967_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(
                    v_e_953_, v___x_966_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_,
                    v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_,
                );
                if lean_obj_tag(v___x_967_) == 0 {
                    v_isSharedCheck_975_ = (!lean_is_exclusive(v___x_967_)) as u8;
                    if v_isSharedCheck_975_ == 0 {
                        v_unused_976_ = lean_ctor_get(v___x_967_, 0);
                        lean_dec(v_unused_976_);
                        v___x_969_ = v___x_967_;
                        v_isShared_970_ = v_isSharedCheck_975_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_967_);
                        v___x_969_ = lean_box(0);
                        v_isShared_970_ = v_isSharedCheck_975_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_977_ = lean_ctor_get(v___x_967_, 0);
                    v_isSharedCheck_984_ = (!lean_is_exclusive(v___x_967_)) as u8;
                    if v_isSharedCheck_984_ == 0 {
                        v___x_979_ = v___x_967_;
                        v_isShared_980_ = v_isSharedCheck_984_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_977_);
                        lean_dec(v___x_967_);
                        v___x_979_ = lean_box(0);
                        v_isShared_980_ = v_isSharedCheck_984_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_971_ = lean_box(0);
                if v_isShared_970_ == 0 {
                    lean_ctor_set(v___x_969_, 0, v___x_971_);
                    v___x_973_ = v___x_969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
                    v___x_973_ = v_reuseFailAlloc_974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_973_;
            }
            3 => {
                if v_isShared_980_ == 0 {
                    v___x_982_ = v___x_979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
                    v___x_982_ = v_reuseFailAlloc_983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar___boxed(
    mut v_e_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
    mut v_a_993_: *mut LeanObject,
    mut v_a_994_: *mut LeanObject,
    mut v_a_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_998_: *mut LeanObject = core::ptr::null_mut();
    v_res_998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
    lean_dec(v_a_996_);
    lean_dec_ref(v_a_995_);
    lean_dec(v_a_994_);
    lean_dec_ref(v_a_993_);
    lean_dec(v_a_992_);
    lean_dec_ref(v_a_991_);
    lean_dec(v_a_990_);
    lean_dec_ref(v_a_989_);
    lean_dec(v_a_988_);
    lean_dec(v_a_987_);
    lean_dec(v_a_986_);
    return v_res_998_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(
    mut v_e_999_: *mut LeanObject,
) -> u8 {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v_arg_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v_arg_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: u8 = 0;
    let mut v___x_1014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1000_ = l_Lean_Expr_cleanupAnnotations(v_e_999_);
                v___x_1001_ = l_Lean_Expr_isApp(v___x_1000_);
                if v___x_1001_ == 0 {
                    lean_dec_ref(v___x_1000_);
                    return v___x_1001_;
                } else {
                    v_arg_1002_ = lean_ctor_get(v___x_1000_, 1);
                    lean_inc_ref(v_arg_1002_);
                    v___x_1003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1000_);
                    v___x_1004_ = l_Lean_Expr_isApp(v___x_1003_);
                    if v___x_1004_ == 0 {
                        lean_dec_ref(v___x_1003_);
                        lean_dec_ref(v_arg_1002_);
                        return v___x_1004_;
                    } else {
                        v_arg_1005_ = lean_ctor_get(v___x_1003_, 1);
                        lean_inc_ref(v_arg_1005_);
                        v___x_1006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1003_);
                        v___x_1007_ = l_Lean_Expr_isApp(v___x_1006_);
                        if v___x_1007_ == 0 {
                            lean_dec_ref(v___x_1006_);
                            lean_dec_ref(v_arg_1005_);
                            lean_dec_ref(v_arg_1002_);
                            return v___x_1007_;
                        } else {
                            v___x_1008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1006_);
                            v___x_1009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14;
                            v___x_1010_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1009_);
                            if v___x_1010_ == 0 {
                                lean_dec_ref(v_arg_1005_);
                                v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17;
                                v___x_1012_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1011_);
                                lean_dec_ref(v___x_1008_);
                                if v___x_1012_ == 0 {
                                    lean_dec_ref(v_arg_1002_);
                                    return v___x_1012_;
                                } else {
                                    v_e_999_ = v_arg_1002_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_1008_);
                                lean_dec_ref(v_arg_1002_);
                                v___x_1014_ = l_Lean_Meta_Grind_Arith_isNatNum(v_arg_1005_);
                                return v___x_1014_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral___boxed(
    mut v_e_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1016_: u8 = 0;
    let mut v_r_1017_: *mut LeanObject = core::ptr::null_mut();
    v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_e_1015_);
    v_r_1017_ = lean_box((v_res_1016_) as usize);
    return v_r_1017_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_markVars(
    mut v_e_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_a_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: u8 = 0;
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: u8 = 0;
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1118_: u8 = 0;
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1136_: u8 = 0;
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut v_unused_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1160_: u8 = 0;
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: u8 = 0;
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_a_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v_a_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1018_);
                v___x_1034_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1018_, v_a_1027_);
                if lean_obj_tag(v___x_1034_) == 0 {
                    v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
                    lean_inc(v_a_1035_);
                    lean_dec_ref_known(v___x_1034_, 1);
                    v___x_1036_ = l_Lean_Expr_cleanupAnnotations(v_a_1035_);
                    v___x_1037_ = l_Lean_Expr_isApp(v___x_1036_);
                    if v___x_1037_ == 0 {
                        lean_dec_ref(v___x_1036_);
                        v___x_1038_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                        return v___x_1038_;
                    } else {
                        v_arg_1039_ = lean_ctor_get(v___x_1036_, 1);
                        lean_inc_ref(v_arg_1039_);
                        v___x_1040_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1036_);
                        v___x_1041_ = l_Lean_Expr_isApp(v___x_1040_);
                        if v___x_1041_ == 0 {
                            lean_dec_ref(v___x_1040_);
                            lean_dec_ref(v_arg_1039_);
                            v___x_1042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                            return v___x_1042_;
                        } else {
                            v_arg_1043_ = lean_ctor_get(v___x_1040_, 1);
                            lean_inc_ref(v_arg_1043_);
                            v___x_1044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1040_);
                            v___x_1045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__5;
                            v___x_1046_ = l_Lean_Expr_isConstOf(v___x_1044_, v___x_1045_);
                            if v___x_1046_ == 0 {
                                v___x_1047_ = l_Lean_Expr_isApp(v___x_1044_);
                                if v___x_1047_ == 0 {
                                    lean_dec_ref(v___x_1044_);
                                    lean_dec_ref(v_arg_1043_);
                                    lean_dec_ref(v_arg_1039_);
                                    v___x_1048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                    return v___x_1048_;
                                } else {
                                    v_arg_1049_ = lean_ctor_get(v___x_1044_, 1);
                                    lean_inc_ref(v_arg_1049_);
                                    v___x_1086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1044_);
                                    v___x_1087_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__14;
                                    v___x_1088_ = l_Lean_Expr_isConstOf(v___x_1086_, v___x_1087_);
                                    if v___x_1088_ == 0 {
                                        v___x_1089_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__17;
                                        v___x_1090_ =
                                            l_Lean_Expr_isConstOf(v___x_1086_, v___x_1089_);
                                        if v___x_1090_ == 0 {
                                            v___x_1091_ = l_Lean_Expr_isApp(v___x_1086_);
                                            if v___x_1091_ == 0 {
                                                lean_dec_ref(v___x_1086_);
                                                lean_dec_ref(v_arg_1049_);
                                                lean_dec_ref(v_arg_1043_);
                                                lean_dec_ref(v_arg_1039_);
                                                v___x_1092_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                return v___x_1092_;
                                            } else {
                                                v___x_1093_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_1086_);
                                                v___x_1094_ = l_Lean_Expr_isApp(v___x_1093_);
                                                if v___x_1094_ == 0 {
                                                    lean_dec_ref(v___x_1093_);
                                                    lean_dec_ref(v_arg_1049_);
                                                    lean_dec_ref(v_arg_1043_);
                                                    lean_dec_ref(v_arg_1039_);
                                                    v___x_1095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                    return v___x_1095_;
                                                } else {
                                                    v___x_1096_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_1093_,
                                                    );
                                                    v___x_1097_ = l_Lean_Expr_isApp(v___x_1096_);
                                                    if v___x_1097_ == 0 {
                                                        lean_dec_ref(v___x_1096_);
                                                        lean_dec_ref(v_arg_1049_);
                                                        lean_dec_ref(v_arg_1043_);
                                                        lean_dec_ref(v_arg_1039_);
                                                        v___x_1098_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                        return v___x_1098_;
                                                    } else {
                                                        v___x_1099_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_1096_,
                                                            );
                                                        v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__20;
                                                        v___x_1101_ = l_Lean_Expr_isConstOf(
                                                            v___x_1099_,
                                                            v___x_1100_,
                                                        );
                                                        if v___x_1101_ == 0 {
                                                            v___x_1102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__23;
                                                            v___x_1103_ = l_Lean_Expr_isConstOf(
                                                                v___x_1099_,
                                                                v___x_1102_,
                                                            );
                                                            if v___x_1103_ == 0 {
                                                                v___x_1104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__26;
                                                                v___x_1105_ = l_Lean_Expr_isConstOf(
                                                                    v___x_1099_,
                                                                    v___x_1104_,
                                                                );
                                                                if v___x_1105_ == 0 {
                                                                    v___x_1106_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f___closed__29;
                                                                    v___x_1107_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_1099_,
                                                                            v___x_1106_,
                                                                        );
                                                                    lean_dec_ref(v___x_1099_);
                                                                    if v___x_1107_ == 0 {
                                                                        lean_dec_ref(v_arg_1049_);
                                                                        lean_dec_ref(v_arg_1043_);
                                                                        lean_dec_ref(v_arg_1039_);
                                                                        v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                        return v___x_1108_;
                                                                    } else {
                                                                        v___x_1109_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                        if lean_obj_tag(v___x_1109_)
                                                                            == 0
                                                                        {
                                                                            v_a_1110_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1109_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_1110_);
                                                                            lean_dec_ref_known(
                                                                                v___x_1109_,
                                                                                1,
                                                                            );
                                                                            v___x_1111_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1110_, v_arg_1049_);
                                                                            lean_dec_ref(
                                                                                v_arg_1049_,
                                                                            );
                                                                            lean_dec(v_a_1110_);
                                                                            if v___x_1111_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_arg_1043_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1039_,
                                                                                );
                                                                                v___x_1112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                return v___x_1112_;
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_e_1018_,
                                                                                );
                                                                                v___x_1113_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_1043_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1113_,
                                                                                ) == 0
                                                                                {
                                                                                    lean_dec_ref_known(v___x_1113_, 1);
                                                                                    v_e_1018_ =
                                                                                        v_arg_1039_;
                                                                                    state = 0;
                                                                                    continue;
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1039_,
                                                                                    );
                                                                                    return v___x_1113_;
                                                                                }
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1049_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1043_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1039_,
                                                                            );
                                                                            lean_dec_ref(v_e_1018_);
                                                                            v_a_1115_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1109_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_1122_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1109_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_1122_
                                                                                == 0
                                                                            {
                                                                                v___x_1117_ =
                                                                                    v___x_1109_;
                                                                                v_isShared_1118_ = v_isSharedCheck_1122_;
                                                                                state = 7;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1115_);
                                                                                lean_dec(
                                                                                    v___x_1109_,
                                                                                );
                                                                                v___x_1117_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1118_ = v_isSharedCheck_1122_;
                                                                                state = 7;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v___x_1099_);
                                                                    v___x_1123_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                    if lean_obj_tag(v___x_1123_)
                                                                        == 0
                                                                    {
                                                                        v_a_1124_ = lean_ctor_get(
                                                                            v___x_1123_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_1124_);
                                                                        lean_dec_ref_known(
                                                                            v___x_1123_,
                                                                            1,
                                                                        );
                                                                        v___x_1125_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_a_1124_, v_arg_1049_);
                                                                        lean_dec_ref(v_arg_1049_);
                                                                        lean_dec(v_a_1124_);
                                                                        if v___x_1125_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_1043_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1039_,
                                                                            );
                                                                            v___x_1126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                            return v___x_1126_;
                                                                        } else {
                                                                            lean_dec_ref(v_e_1018_);
                                                                            v___x_1127_ = l_Lean_Meta_Grind_Arith_Linear_markVars(v_arg_1043_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                            if lean_obj_tag(
                                                                                v___x_1127_,
                                                                            ) == 0
                                                                            {
                                                                                lean_dec_ref_known(
                                                                                    v___x_1127_,
                                                                                    1,
                                                                                );
                                                                                v_e_1018_ =
                                                                                    v_arg_1039_;
                                                                                state = 0;
                                                                                continue;
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1039_,
                                                                                );
                                                                                return v___x_1127_;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1049_);
                                                                        lean_dec_ref(v_arg_1043_);
                                                                        lean_dec_ref(v_arg_1039_);
                                                                        lean_dec_ref(v_e_1018_);
                                                                        v_a_1129_ = lean_ctor_get(
                                                                            v___x_1123_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1136_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1123_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1136_
                                                                            == 0
                                                                        {
                                                                            v___x_1131_ =
                                                                                v___x_1123_;
                                                                            v_isShared_1132_ = v_isSharedCheck_1136_;
                                                                            state = 9;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1129_);
                                                                            lean_dec(v___x_1123_);
                                                                            v___x_1131_ =
                                                                                lean_box(0);
                                                                            v_isShared_1132_ = v_isSharedCheck_1136_;
                                                                            state = 9;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_1099_);
                                                                v___x_1137_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                if lean_obj_tag(v___x_1137_) == 0 {
                                                                    v_a_1138_ = lean_ctor_get(
                                                                        v___x_1137_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_a_1138_);
                                                                    lean_dec_ref_known(
                                                                        v___x_1137_,
                                                                        1,
                                                                    );
                                                                    v___x_1139_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_a_1138_, v_arg_1049_);
                                                                    lean_dec_ref(v_arg_1049_);
                                                                    lean_dec(v_a_1138_);
                                                                    if v___x_1139_ == 0 {
                                                                        lean_dec_ref(v_arg_1043_);
                                                                        lean_dec_ref(v_arg_1039_);
                                                                        v___x_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                        return v___x_1140_;
                                                                    } else {
                                                                        lean_inc_ref(v_arg_1043_);
                                                                        v___x_1141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_1043_);
                                                                        if v___x_1141_ == 0 {
                                                                            lean_inc_ref(
                                                                                v_arg_1039_,
                                                                            );
                                                                            v___x_1142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_isNumeral(v_arg_1039_);
                                                                            if v___x_1142_ == 0 {
                                                                                v___x_1143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1043_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                if lean_obj_tag(
                                                                                    v___x_1143_,
                                                                                ) == 0
                                                                                {
                                                                                    lean_dec_ref_known(v___x_1143_, 1);
                                                                                    v___x_1144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1039_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                    if lean_obj_tag(
                                                                                        v___x_1144_,
                                                                                    ) == 0
                                                                                    {
                                                                                        lean_dec_ref_known(v___x_1144_, 1);
                                                                                        v___x_1145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                        if lean_obj_tag(v___x_1145_) == 0 {
v_isSharedCheck_1153_ = (!lean_is_exclusive(v___x_1145_)) as u8;
if v_isSharedCheck_1153_ == 0 {
v_unused_1154_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1154_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1153_;
state = 11; continue;
} else {
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
state = 11; continue;
}
} else {
return v___x_1145_;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_e_1018_);
                                                                                        return v___x_1144_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1039_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_e_1018_,
                                                                                    );
                                                                                    return v___x_1143_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1039_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_e_1018_,
                                                                                );
                                                                                v___x_1155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1043_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                                return v___x_1155_;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1043_,
                                                                            );
                                                                            lean_dec_ref(v_e_1018_);
                                                                            v___x_1156_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1039_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                                            return v___x_1156_;
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_1049_);
                                                                    lean_dec_ref(v_arg_1043_);
                                                                    lean_dec_ref(v_arg_1039_);
                                                                    lean_dec_ref(v_e_1018_);
                                                                    v_a_1157_ = lean_ctor_get(
                                                                        v___x_1137_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1164_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1137_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1164_ == 0 {
                                                                        v___x_1159_ = v___x_1137_;
                                                                        v_isShared_1160_ =
                                                                            v_isSharedCheck_1164_;
                                                                        state = 13;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1157_);
                                                                        lean_dec(v___x_1137_);
                                                                        v___x_1159_ = lean_box(0);
                                                                        v_isShared_1160_ =
                                                                            v_isSharedCheck_1164_;
                                                                        state = 13;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___x_1099_);
                                                            v___x_1165_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                                                            if lean_obj_tag(v___x_1165_) == 0 {
                                                                v_a_1166_ =
                                                                    lean_ctor_get(v___x_1165_, 0);
                                                                lean_inc(v_a_1166_);
                                                                lean_dec_ref_known(v___x_1165_, 1);
                                                                v___x_1167_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_a_1166_, v_arg_1049_);
                                                                lean_dec(v_a_1166_);
                                                                if v___x_1167_ == 0 {
                                                                    v___y_1051_ = v_a_1019_;
                                                                    v___y_1052_ = v_a_1020_;
                                                                    v___y_1053_ = v_a_1021_;
                                                                    v___y_1054_ = v_a_1022_;
                                                                    v___y_1055_ = v_a_1023_;
                                                                    v___y_1056_ = v_a_1024_;
                                                                    v___y_1057_ = v_a_1025_;
                                                                    v___y_1058_ = v_a_1026_;
                                                                    v___y_1059_ = v_a_1027_;
                                                                    v___y_1060_ = v_a_1028_;
                                                                    v___y_1061_ = v_a_1029_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    lean_inc_ref(v_arg_1043_);
                                                                    v___x_1168_ =
                                                                        l_Lean_Meta_getIntValue_x3f(
                                                                            v_arg_1043_,
                                                                            v_a_1026_,
                                                                            v_a_1027_,
                                                                            v_a_1028_,
                                                                            v_a_1029_,
                                                                        );
                                                                    if lean_obj_tag(v___x_1168_)
                                                                        == 0
                                                                    {
                                                                        v_a_1169_ = lean_ctor_get(
                                                                            v___x_1168_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_1169_);
                                                                        lean_dec_ref_known(
                                                                            v___x_1168_,
                                                                            1,
                                                                        );
                                                                        if lean_obj_tag(v_a_1169_)
                                                                            == 0
                                                                        {
                                                                            v___y_1171_ =
                                                                                v___x_1090_;
                                                                            state = 15;
                                                                            continue;
                                                                        } else {
                                                                            lean_dec_ref_known(
                                                                                v_a_1169_, 1,
                                                                            );
                                                                            v___y_1171_ =
                                                                                v___x_1167_;
                                                                            state = 15;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1049_);
                                                                        lean_dec_ref(v_arg_1043_);
                                                                        lean_dec_ref(v_arg_1039_);
                                                                        lean_dec_ref(v_e_1018_);
                                                                        v_a_1173_ = lean_ctor_get(
                                                                            v___x_1168_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1180_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1168_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1180_
                                                                            == 0
                                                                        {
                                                                            v___x_1175_ =
                                                                                v___x_1168_;
                                                                            v_isShared_1176_ = v_isSharedCheck_1180_;
                                                                            state = 16;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1173_);
                                                                            lean_dec(v___x_1168_);
                                                                            v___x_1175_ =
                                                                                lean_box(0);
                                                                            v_isShared_1176_ = v_isSharedCheck_1180_;
                                                                            state = 16;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_1049_);
                                                                lean_dec_ref(v_arg_1043_);
                                                                lean_dec_ref(v_arg_1039_);
                                                                lean_dec_ref(v_e_1018_);
                                                                v_a_1181_ =
                                                                    lean_ctor_get(v___x_1165_, 0);
                                                                v_isSharedCheck_1188_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1165_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1188_ == 0 {
                                                                    v___x_1183_ = v___x_1165_;
                                                                    v_isShared_1184_ =
                                                                        v_isSharedCheck_1188_;
                                                                    state = 18;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_1181_);
                                                                    lean_dec(v___x_1165_);
                                                                    v___x_1183_ = lean_box(0);
                                                                    v_isShared_1184_ =
                                                                        v_isSharedCheck_1188_;
                                                                    state = 18;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1086_);
                                            lean_dec_ref(v_arg_1049_);
                                            lean_dec_ref(v_arg_1043_);
                                            lean_dec_ref(v_e_1018_);
                                            v_e_1018_ = v_arg_1039_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v___x_1086_);
                                        lean_dec_ref(v_arg_1049_);
                                        lean_dec_ref(v_arg_1043_);
                                        lean_dec_ref(v_arg_1039_);
                                        lean_dec_ref(v_e_1018_);
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_1044_);
                                lean_dec_ref(v_arg_1043_);
                                lean_dec_ref(v_arg_1039_);
                                lean_dec_ref(v_e_1018_);
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1018_);
                    v_a_1190_ = lean_ctor_get(v___x_1034_, 0);
                    v_isSharedCheck_1197_ = (!lean_is_exclusive(v___x_1034_)) as u8;
                    if v_isSharedCheck_1197_ == 0 {
                        v___x_1192_ = v___x_1034_;
                        v_isShared_1193_ = v_isSharedCheck_1197_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_1190_);
                        lean_dec(v___x_1034_);
                        v___x_1192_ = lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1197_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1032_ = lean_box(0);
                v___x_1033_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1033_, 0, v___x_1032_);
                return v___x_1033_;
            }
            2 => {
                v___x_1062_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v___y_1051_,
                    v___y_1052_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                    v___y_1056_,
                    v___y_1057_,
                    v___y_1058_,
                    v___y_1059_,
                    v___y_1060_,
                    v___y_1061_,
                );
                if lean_obj_tag(v___x_1062_) == 0 {
                    v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
                    lean_inc(v_a_1063_);
                    lean_dec_ref_known(v___x_1062_, 1);
                    v___x_1064_ =
                        l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_a_1063_, v_arg_1049_);
                    lean_dec_ref(v_arg_1049_);
                    lean_dec(v_a_1063_);
                    if v___x_1064_ == 0 {
                        lean_dec_ref(v_arg_1043_);
                        lean_dec_ref(v_arg_1039_);
                        v___x_1065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
                        return v___x_1065_;
                    } else {
                        v___x_1066_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_1043_,
                            v___y_1058_,
                            v___y_1059_,
                            v___y_1060_,
                            v___y_1061_,
                        );
                        lean_dec_ref(v_arg_1043_);
                        if lean_obj_tag(v___x_1066_) == 0 {
                            v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
                            lean_inc(v_a_1067_);
                            lean_dec_ref_known(v___x_1066_, 1);
                            if lean_obj_tag(v_a_1067_) == 0 {
                                lean_dec_ref(v_arg_1039_);
                                v___x_1068_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_e_1018_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
                                return v___x_1068_;
                            } else {
                                lean_dec_ref_known(v_a_1067_, 1);
                                lean_dec_ref(v_e_1018_);
                                v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1039_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
                                return v___x_1069_;
                            }
                        } else {
                            lean_dec_ref(v_arg_1039_);
                            lean_dec_ref(v_e_1018_);
                            v_a_1070_ = lean_ctor_get(v___x_1066_, 0);
                            v_isSharedCheck_1077_ = (!lean_is_exclusive(v___x_1066_)) as u8;
                            if v_isSharedCheck_1077_ == 0 {
                                v___x_1072_ = v___x_1066_;
                                v_isShared_1073_ = v_isSharedCheck_1077_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1070_);
                                lean_dec(v___x_1066_);
                                v___x_1072_ = lean_box(0);
                                v_isShared_1073_ = v_isSharedCheck_1077_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_1049_);
                    lean_dec_ref(v_arg_1043_);
                    lean_dec_ref(v_arg_1039_);
                    lean_dec_ref(v_e_1018_);
                    v_a_1078_ = lean_ctor_get(v___x_1062_, 0);
                    v_isSharedCheck_1085_ = (!lean_is_exclusive(v___x_1062_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1080_ = v___x_1062_;
                        v_isShared_1081_ = v_isSharedCheck_1085_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1078_);
                        lean_dec(v___x_1062_);
                        v___x_1080_ = lean_box(0);
                        v_isShared_1081_ = v_isSharedCheck_1085_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1073_ == 0 {
                    v___x_1075_ = v___x_1072_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
                    v___x_1075_ = v_reuseFailAlloc_1076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1075_;
            }
            5 => {
                if v_isShared_1081_ == 0 {
                    v___x_1083_ = v___x_1080_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1083_;
            }
            7 => {
                if v_isShared_1118_ == 0 {
                    v___x_1120_ = v___x_1117_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
                    v___x_1120_ = v_reuseFailAlloc_1121_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1120_;
            }
            9 => {
                if v_isShared_1132_ == 0 {
                    v___x_1134_ = v___x_1131_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
                    v___x_1134_ = v_reuseFailAlloc_1135_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1134_;
            }
            11 => {
                v___x_1149_ = lean_box(0);
                if v_isShared_1148_ == 0 {
                    lean_ctor_set(v___x_1147_, 0, v___x_1149_);
                    v___x_1151_ = v___x_1147_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
                    v___x_1151_ = v_reuseFailAlloc_1152_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1151_;
            }
            13 => {
                if v_isShared_1160_ == 0 {
                    v___x_1162_ = v___x_1159_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
                    v___x_1162_ = v_reuseFailAlloc_1163_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1162_;
            }
            15 => {
                if v___y_1171_ == 0 {
                    v___y_1051_ = v_a_1019_;
                    v___y_1052_ = v_a_1020_;
                    v___y_1053_ = v_a_1021_;
                    v___y_1054_ = v_a_1022_;
                    v___y_1055_ = v_a_1023_;
                    v___y_1056_ = v_a_1024_;
                    v___y_1057_ = v_a_1025_;
                    v___y_1058_ = v_a_1026_;
                    v___y_1059_ = v_a_1027_;
                    v___y_1060_ = v_a_1028_;
                    v___y_1061_ = v_a_1029_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_arg_1049_);
                    lean_dec_ref(v_arg_1043_);
                    lean_dec_ref(v_e_1018_);
                    v___x_1172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_markVars_markVar(v_arg_1039_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
                    return v___x_1172_;
                }
            }
            16 => {
                if v_isShared_1176_ == 0 {
                    v___x_1178_ = v___x_1175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1178_;
            }
            18 => {
                if v_isShared_1184_ == 0 {
                    v___x_1186_ = v___x_1183_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
                    v___x_1186_ = v_reuseFailAlloc_1187_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1186_;
            }
            20 => {
                if v_isShared_1193_ == 0 {
                    v___x_1195_ = v___x_1192_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
                    v___x_1195_ = v_reuseFailAlloc_1196_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_markVars___boxed(
    mut v_e_1198_: *mut LeanObject,
    mut v_a_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
    mut v_a_1203_: *mut LeanObject,
    mut v_a_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
    mut v_a_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1211_: *mut LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Lean_Meta_Grind_Arith_Linear_markVars(
        v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_,
        v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_,
    );
    lean_dec(v_a_1209_);
    lean_dec_ref(v_a_1208_);
    lean_dec(v_a_1207_);
    lean_dec_ref(v_a_1206_);
    lean_dec(v_a_1205_);
    lean_dec_ref(v_a_1204_);
    lean_dec(v_a_1203_);
    lean_dec_ref(v_a_1202_);
    lean_dec(v_a_1201_);
    lean_dec(v_a_1200_);
    lean_dec(v_a_1199_);
    return v_res_1211_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(
    mut v_msgData_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    v___x_1218_ = lean_st_ref_get(v___y_1216_);
    v_env_1219_ = lean_ctor_get(v___x_1218_, 0);
    lean_inc_ref(v_env_1219_);
    lean_dec(v___x_1218_);
    v___x_1220_ = lean_st_ref_get(v___y_1214_);
    v_mctx_1221_ = lean_ctor_get(v___x_1220_, 0);
    lean_inc_ref(v_mctx_1221_);
    lean_dec(v___x_1220_);
    v_lctx_1222_ = lean_ctor_get(v___y_1213_, 2);
    v_options_1223_ = lean_ctor_get(v___y_1215_, 2);
    lean_inc_ref(v_options_1223_);
    lean_inc_ref(v_lctx_1222_);
    v___x_1224_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1224_, 0, v_env_1219_);
    lean_ctor_set(v___x_1224_, 1, v_mctx_1221_);
    lean_ctor_set(v___x_1224_, 2, v_lctx_1222_);
    lean_ctor_set(v___x_1224_, 3, v_options_1223_);
    v___x_1225_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1225_, 0, v___x_1224_);
    lean_ctor_set(v___x_1225_, 1, v_msgData_1212_);
    v___x_1226_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1226_, 0, v___x_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0___boxed(
    mut v_msgData_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1233_: *mut LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msgData_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
    lean_dec(v___y_1231_);
    lean_dec_ref(v___y_1230_);
    lean_dec(v___y_1229_);
    lean_dec_ref(v___y_1228_);
    return v_res_1233_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: f64 = 0.0;
    v___x_1234_ = lean_unsigned_to_nat(0);
    v___x_1235_ = lean_float_of_nat(v___x_1234_);
    return v___x_1235_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(
    mut v_cls_1239_: *mut LeanObject,
    mut v_msg_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1264_: u8 = 0;
    let mut v_tid_1265_: u64 = 0;
    let mut v_traces_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: f64 = 0.0;
    let mut v___x_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1246_ = lean_ctor_get(v___y_1243_, 5);
                v___x_1247_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msg_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
                v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
                v_isSharedCheck_1292_ = (!lean_is_exclusive(v___x_1247_)) as u8;
                if v_isSharedCheck_1292_ == 0 {
                    v___x_1250_ = v___x_1247_;
                    v_isShared_1251_ = v_isSharedCheck_1292_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1248_);
                    lean_dec(v___x_1247_);
                    v___x_1250_ = lean_box(0);
                    v_isShared_1251_ = v_isSharedCheck_1292_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1252_ = lean_st_ref_take(v___y_1244_);
                v_traceState_1253_ = lean_ctor_get(v___x_1252_, 4);
                v_env_1254_ = lean_ctor_get(v___x_1252_, 0);
                v_nextMacroScope_1255_ = lean_ctor_get(v___x_1252_, 1);
                v_ngen_1256_ = lean_ctor_get(v___x_1252_, 2);
                v_auxDeclNGen_1257_ = lean_ctor_get(v___x_1252_, 3);
                v_cache_1258_ = lean_ctor_get(v___x_1252_, 5);
                v_messages_1259_ = lean_ctor_get(v___x_1252_, 6);
                v_infoState_1260_ = lean_ctor_get(v___x_1252_, 7);
                v_snapshotTasks_1261_ = lean_ctor_get(v___x_1252_, 8);
                v_isSharedCheck_1291_ = (!lean_is_exclusive(v___x_1252_)) as u8;
                if v_isSharedCheck_1291_ == 0 {
                    v___x_1263_ = v___x_1252_;
                    v_isShared_1264_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1261_);
                    lean_inc(v_infoState_1260_);
                    lean_inc(v_messages_1259_);
                    lean_inc(v_cache_1258_);
                    lean_inc(v_traceState_1253_);
                    lean_inc(v_auxDeclNGen_1257_);
                    lean_inc(v_ngen_1256_);
                    lean_inc(v_nextMacroScope_1255_);
                    lean_inc(v_env_1254_);
                    lean_dec(v___x_1252_);
                    v___x_1263_ = lean_box(0);
                    v_isShared_1264_ = v_isSharedCheck_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1265_ = lean_ctor_get_uint64(
                    v_traceState_1253_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_1266_ = lean_ctor_get(v_traceState_1253_, 0);
                v_isSharedCheck_1290_ = (!lean_is_exclusive(v_traceState_1253_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1268_ = v_traceState_1253_;
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_1266_);
                    lean_dec(v_traceState_1253_);
                    v___x_1268_ = lean_box(0);
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1270_ = lean_box(0);
                v___x_1271_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0);
                v___x_1272_ = 0;
                v___x_1273_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1;
                v___x_1274_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_1274_, 0, v_cls_1239_);
                lean_ctor_set(v___x_1274_, 1, v___x_1270_);
                lean_ctor_set(v___x_1274_, 2, v___x_1273_);
                lean_ctor_set_float(
                    v___x_1274_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1271_,
                );
                lean_ctor_set_float(
                    v___x_1274_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_1271_,
                );
                lean_ctor_set_uint8(
                    v___x_1274_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_1272_,
                );
                v___x_1275_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2;
                v___x_1276_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_1276_, 0, v___x_1274_);
                lean_ctor_set(v___x_1276_, 1, v_a_1248_);
                lean_ctor_set(v___x_1276_, 2, v___x_1275_);
                lean_inc(v_ref_1246_);
                v___x_1277_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1277_, 0, v_ref_1246_);
                lean_ctor_set(v___x_1277_, 1, v___x_1276_);
                v___x_1278_ = l_Lean_PersistentArray_push___redArg(v_traces_1266_, v___x_1277_);
                if v_isShared_1269_ == 0 {
                    lean_ctor_set(v___x_1268_, 0, v___x_1278_);
                    v___x_1280_ = v___x_1268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1278_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_1289_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_1265_,
                    );
                    v___x_1280_ = v_reuseFailAlloc_1289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1264_ == 0 {
                    lean_ctor_set(v___x_1263_, 4, v___x_1280_);
                    v___x_1282_ = v___x_1263_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_env_1254_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_nextMacroScope_1255_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_ngen_1256_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_auxDeclNGen_1257_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 4, v___x_1280_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 5, v_cache_1258_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 6, v_messages_1259_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 7, v_infoState_1260_);
                    lean_ctor_set(v_reuseFailAlloc_1288_, 8, v_snapshotTasks_1261_);
                    v___x_1282_ = v_reuseFailAlloc_1288_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1283_ = lean_st_ref_set(v___y_1244_, v___x_1282_);
                v___x_1284_ = lean_box(0);
                if v_isShared_1251_ == 0 {
                    lean_ctor_set(v___x_1250_, 0, v___x_1284_);
                    v___x_1286_ = v___x_1250_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
                    v___x_1286_ = v_reuseFailAlloc_1287_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___boxed(
    mut v_cls_1293_: *mut LeanObject,
    mut v_msg_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(
            v_cls_1293_,
            v_msg_1294_,
            v___y_1295_,
            v___y_1296_,
            v___y_1297_,
            v___y_1298_,
        );
    lean_dec(v___y_1298_);
    lean_dec_ref(v___y_1297_);
    lean_dec(v___y_1296_);
    lean_dec_ref(v___y_1295_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(
    mut v_cls_1301_: *mut LeanObject,
    mut v_msg_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1313_: u8 = 0;
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v_tid_1327_: u64 = 0;
    let mut v_traces_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: f64 = 0.0;
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1308_ = lean_ctor_get(v___y_1305_, 5);
                v___x_1309_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0_spec__0(v_msg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
                v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
                v_isSharedCheck_1354_ = (!lean_is_exclusive(v___x_1309_)) as u8;
                if v_isSharedCheck_1354_ == 0 {
                    v___x_1312_ = v___x_1309_;
                    v_isShared_1313_ = v_isSharedCheck_1354_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1310_);
                    lean_dec(v___x_1309_);
                    v___x_1312_ = lean_box(0);
                    v_isShared_1313_ = v_isSharedCheck_1354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1314_ = lean_st_ref_take(v___y_1306_);
                v_traceState_1315_ = lean_ctor_get(v___x_1314_, 4);
                v_env_1316_ = lean_ctor_get(v___x_1314_, 0);
                v_nextMacroScope_1317_ = lean_ctor_get(v___x_1314_, 1);
                v_ngen_1318_ = lean_ctor_get(v___x_1314_, 2);
                v_auxDeclNGen_1319_ = lean_ctor_get(v___x_1314_, 3);
                v_cache_1320_ = lean_ctor_get(v___x_1314_, 5);
                v_messages_1321_ = lean_ctor_get(v___x_1314_, 6);
                v_infoState_1322_ = lean_ctor_get(v___x_1314_, 7);
                v_snapshotTasks_1323_ = lean_ctor_get(v___x_1314_, 8);
                v_isSharedCheck_1353_ = (!lean_is_exclusive(v___x_1314_)) as u8;
                if v_isSharedCheck_1353_ == 0 {
                    v___x_1325_ = v___x_1314_;
                    v_isShared_1326_ = v_isSharedCheck_1353_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1323_);
                    lean_inc(v_infoState_1322_);
                    lean_inc(v_messages_1321_);
                    lean_inc(v_cache_1320_);
                    lean_inc(v_traceState_1315_);
                    lean_inc(v_auxDeclNGen_1319_);
                    lean_inc(v_ngen_1318_);
                    lean_inc(v_nextMacroScope_1317_);
                    lean_inc(v_env_1316_);
                    lean_dec(v___x_1314_);
                    v___x_1325_ = lean_box(0);
                    v_isShared_1326_ = v_isSharedCheck_1353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1327_ = lean_ctor_get_uint64(
                    v_traceState_1315_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_1328_ = lean_ctor_get(v_traceState_1315_, 0);
                v_isSharedCheck_1352_ = (!lean_is_exclusive(v_traceState_1315_)) as u8;
                if v_isSharedCheck_1352_ == 0 {
                    v___x_1330_ = v_traceState_1315_;
                    v_isShared_1331_ = v_isSharedCheck_1352_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_1328_);
                    lean_dec(v_traceState_1315_);
                    v___x_1330_ = lean_box(0);
                    v_isShared_1331_ = v_isSharedCheck_1352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1332_ = lean_box(0);
                v___x_1333_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__0);
                v___x_1334_ = 0;
                v___x_1335_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__1;
                v___x_1336_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_1336_, 0, v_cls_1301_);
                lean_ctor_set(v___x_1336_, 1, v___x_1332_);
                lean_ctor_set(v___x_1336_, 2, v___x_1335_);
                lean_ctor_set_float(
                    v___x_1336_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1333_,
                );
                lean_ctor_set_float(
                    v___x_1336_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_1333_,
                );
                lean_ctor_set_uint8(
                    v___x_1336_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_1334_,
                );
                v___x_1337_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg___closed__2;
                v___x_1338_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_1338_, 0, v___x_1336_);
                lean_ctor_set(v___x_1338_, 1, v_a_1310_);
                lean_ctor_set(v___x_1338_, 2, v___x_1337_);
                lean_inc(v_ref_1308_);
                v___x_1339_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1339_, 0, v_ref_1308_);
                lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                v___x_1340_ = l_Lean_PersistentArray_push___redArg(v_traces_1328_, v___x_1339_);
                if v_isShared_1331_ == 0 {
                    lean_ctor_set(v___x_1330_, 0, v___x_1340_);
                    v___x_1342_ = v___x_1330_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1340_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_1351_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_1327_,
                    );
                    v___x_1342_ = v_reuseFailAlloc_1351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1326_ == 0 {
                    lean_ctor_set(v___x_1325_, 4, v___x_1342_);
                    v___x_1344_ = v___x_1325_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_env_1316_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_nextMacroScope_1317_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_ngen_1318_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_auxDeclNGen_1319_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 4, v___x_1342_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_cache_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 6, v_messages_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 7, v_infoState_1322_);
                    lean_ctor_set(v_reuseFailAlloc_1350_, 8, v_snapshotTasks_1323_);
                    v___x_1344_ = v_reuseFailAlloc_1350_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1345_ = lean_st_ref_set(v___y_1306_, v___x_1344_);
                v___x_1346_ = lean_box(0);
                if v_isShared_1313_ == 0 {
                    lean_ctor_set(v___x_1312_, 0, v___x_1346_);
                    v___x_1348_ = v___x_1312_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
                    v___x_1348_ = v_reuseFailAlloc_1349_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg___boxed(
    mut v_cls_1355_: *mut LeanObject,
    mut v_msg_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
    mut v___y_1358_: *mut LeanObject,
    mut v___y_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1362_: *mut LeanObject = core::ptr::null_mut();
    v_res_1362_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(
            v_cls_1355_,
            v_msg_1356_,
            v___y_1357_,
            v___y_1358_,
            v___y_1359_,
            v___y_1360_,
        );
    lean_dec(v___y_1360_);
    lean_dec_ref(v___y_1359_);
    lean_dec(v___y_1358_);
    lean_dec_ref(v___y_1357_);
    return v_res_1362_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6() -> *mut LeanObject {
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    v___x_1373_ = l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3;
    v___x_1374_ = l_Lean_Meta_Grind_Arith_Linear_internalize___closed__5;
    v___x_1375_ = l_Lean_Name_append(v___x_1374_, v___x_1373_);
    return v___x_1375_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8() -> *mut LeanObject {
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_Meta_Grind_Arith_Linear_internalize___closed__7;
    v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
    return v___x_1378_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_internalize(
    mut v_e_1379_: *mut LeanObject,
    mut v_parent_x3f_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
    mut v_a_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v_linarith_1426_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: u8 = 0;
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: u8 = 0;
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1438_: u8 = 0;
    let mut v_val_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v_val_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1456_: u8 = 0;
    let mut v_fst_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v_inheritedTraceOptions_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v_unused_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v_a_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut v_a_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_a_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1421_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1383_);
                if lean_obj_tag(v___x_1421_) == 0 {
                    v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
                    v_isSharedCheck_1516_ = (!lean_is_exclusive(v___x_1421_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1424_ = v___x_1421_;
                        v_isShared_1425_ = v_isSharedCheck_1516_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1422_);
                        lean_dec(v___x_1421_);
                        v___x_1424_ = lean_box(0);
                        v_isShared_1425_ = v_isSharedCheck_1516_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_parent_x3f_1380_);
                    lean_dec_ref(v_e_1379_);
                    v_a_1517_ = lean_ctor_get(v___x_1421_, 0);
                    v_isSharedCheck_1524_ = (!lean_is_exclusive(v___x_1421_)) as u8;
                    if v_isSharedCheck_1524_ == 0 {
                        v___x_1519_ = v___x_1421_;
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_1517_);
                        lean_dec(v___x_1421_);
                        v___x_1519_ = lean_box(0);
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_e_1379_);
                v___x_1404_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(
                    v_e_1379_,
                    v___y_1393_,
                    v___y_1394_,
                    v___y_1398_,
                    v___y_1399_,
                    v___y_1400_,
                    v___y_1401_,
                    v___y_1402_,
                    v___y_1403_,
                );
                if lean_obj_tag(v___x_1404_) == 0 {
                    lean_dec_ref_known(v___x_1404_, 1);
                    v___x_1405_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                    lean_inc_ref(v_e_1379_);
                    v___x_1406_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                        v___x_1405_,
                        v_e_1379_,
                        v___y_1394_,
                        v___y_1395_,
                        v___y_1396_,
                        v___y_1397_,
                        v___y_1398_,
                        v___y_1399_,
                        v___y_1400_,
                        v___y_1401_,
                        v___y_1402_,
                        v___y_1403_,
                    );
                    if lean_obj_tag(v___x_1406_) == 0 {
                        lean_dec_ref_known(v___x_1406_, 1);
                        v___x_1407_ = l_Lean_Meta_Grind_Arith_Linear_markVars(
                            v_e_1379_,
                            v___y_1393_,
                            v___y_1394_,
                            v___y_1395_,
                            v___y_1396_,
                            v___y_1397_,
                            v___y_1398_,
                            v___y_1399_,
                            v___y_1400_,
                            v___y_1401_,
                            v___y_1402_,
                            v___y_1403_,
                        );
                        lean_dec(v___y_1393_);
                        return v___x_1407_;
                    } else {
                        lean_dec(v___y_1393_);
                        lean_dec_ref(v_e_1379_);
                        return v___x_1406_;
                    }
                } else {
                    lean_dec(v___y_1393_);
                    lean_dec_ref(v_e_1379_);
                    return v___x_1404_;
                }
            }
            2 => {
                v___x_1419_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                v___x_1420_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                    v___x_1419_,
                    v_e_1379_,
                    v___y_1409_,
                    v___y_1410_,
                    v___y_1411_,
                    v___y_1412_,
                    v___y_1413_,
                    v___y_1414_,
                    v___y_1415_,
                    v___y_1416_,
                    v___y_1417_,
                    v___y_1418_,
                );
                return v___x_1420_;
            }
            3 => {
                v_linarith_1426_ = lean_ctor_get_uint8(
                    v_a_1422_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
                );
                lean_dec(v_a_1422_);
                if v_linarith_1426_ == 0 {
                    lean_dec(v_parent_x3f_1380_);
                    lean_dec_ref(v_e_1379_);
                    v___x_1427_ = lean_box(0);
                    if v_isShared_1425_ == 0 {
                        lean_ctor_set(v___x_1424_, 0, v___x_1427_);
                        v___x_1429_ = v___x_1424_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
                        v___x_1429_ = v_reuseFailAlloc_1430_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1431_ =
                        l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_1380_);
                    if v___x_1431_ == 0 {
                        lean_inc_ref(v_e_1379_);
                        v___x_1432_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_getType_x3f(v_e_1379_);
                        if lean_obj_tag(v___x_1432_) == 1 {
                            v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
                            lean_inc(v_val_1433_);
                            lean_dec_ref_known(v___x_1432_, 1);
                            v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize_0__Lean_Meta_Grind_Arith_Linear_isForbiddenParent(v_parent_x3f_1380_);
                            if v___x_1434_ == 0 {
                                lean_del_object(v___x_1424_);
                                lean_inc(v_val_1433_);
                                v___x_1435_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(
                                    v_val_1433_,
                                    v_a_1381_,
                                    v_a_1382_,
                                    v_a_1383_,
                                    v_a_1384_,
                                    v_a_1385_,
                                    v_a_1386_,
                                    v_a_1387_,
                                    v_a_1388_,
                                    v_a_1389_,
                                    v_a_1390_,
                                );
                                if lean_obj_tag(v___x_1435_) == 0 {
                                    v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
                                    lean_inc(v_a_1436_);
                                    lean_dec_ref_known(v___x_1435_, 1);
                                    if lean_obj_tag(v_a_1436_) == 1 {
                                        lean_dec(v_val_1433_);
                                        v_options_1437_ = lean_ctor_get(v_a_1389_, 2);
                                        v_hasTrace_1438_ = lean_ctor_get_uint8(
                                            v_options_1437_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        );
                                        if v_hasTrace_1438_ == 0 {
                                            v_val_1439_ = lean_ctor_get(v_a_1436_, 0);
                                            lean_inc(v_val_1439_);
                                            lean_dec_ref_known(v_a_1436_, 1);
                                            v___y_1393_ = v_val_1439_;
                                            v___y_1394_ = v_a_1381_;
                                            v___y_1395_ = v_a_1382_;
                                            v___y_1396_ = v_a_1383_;
                                            v___y_1397_ = v_a_1384_;
                                            v___y_1398_ = v_a_1385_;
                                            v___y_1399_ = v_a_1386_;
                                            v___y_1400_ = v_a_1387_;
                                            v___y_1401_ = v_a_1388_;
                                            v___y_1402_ = v_a_1389_;
                                            v___y_1403_ = v_a_1390_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_val_1440_ = lean_ctor_get(v_a_1436_, 0);
                                            lean_inc(v_val_1440_);
                                            lean_dec_ref_known(v_a_1436_, 1);
                                            v_inheritedTraceOptions_1441_ =
                                                lean_ctor_get(v_a_1389_, 13);
                                            v___x_1442_ = l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3;
                                            v___x_1443_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once), _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6);
                                            v___x_1444_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1441_, v_options_1437_, v___x_1443_);
                                            if v___x_1444_ == 0 {
                                                v___y_1393_ = v_val_1440_;
                                                v___y_1394_ = v_a_1381_;
                                                v___y_1395_ = v_a_1382_;
                                                v___y_1396_ = v_a_1383_;
                                                v___y_1397_ = v_a_1384_;
                                                v___y_1398_ = v_a_1385_;
                                                v___y_1399_ = v_a_1386_;
                                                v___y_1400_ = v_a_1387_;
                                                v___y_1401_ = v_a_1388_;
                                                v___y_1402_ = v_a_1389_;
                                                v___y_1403_ = v_a_1390_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc_ref(v_e_1379_);
                                                v___x_1445_ = l_Lean_MessageData_ofExpr(v_e_1379_);
                                                v___x_1446_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(v___x_1442_, v___x_1445_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
                                                if lean_obj_tag(v___x_1446_) == 0 {
                                                    lean_dec_ref_known(v___x_1446_, 1);
                                                    v___y_1393_ = v_val_1440_;
                                                    v___y_1394_ = v_a_1381_;
                                                    v___y_1395_ = v_a_1382_;
                                                    v___y_1396_ = v_a_1383_;
                                                    v___y_1397_ = v_a_1384_;
                                                    v___y_1398_ = v_a_1385_;
                                                    v___y_1399_ = v_a_1386_;
                                                    v___y_1400_ = v_a_1387_;
                                                    v___y_1401_ = v_a_1388_;
                                                    v___y_1402_ = v_a_1389_;
                                                    v___y_1403_ = v_a_1390_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec(v_val_1440_);
                                                    lean_dec_ref(v_e_1379_);
                                                    return v___x_1446_;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_1436_);
                                        v___x_1447_ =
                                            l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(
                                                v_val_1433_,
                                                v_a_1381_,
                                                v_a_1382_,
                                                v_a_1383_,
                                                v_a_1384_,
                                                v_a_1385_,
                                                v_a_1386_,
                                                v_a_1387_,
                                                v_a_1388_,
                                                v_a_1389_,
                                                v_a_1390_,
                                            );
                                        if lean_obj_tag(v___x_1447_) == 0 {
                                            v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
                                            v_isSharedCheck_1487_ =
                                                (!lean_is_exclusive(v___x_1447_)) as u8;
                                            if v_isSharedCheck_1487_ == 0 {
                                                v___x_1450_ = v___x_1447_;
                                                v_isShared_1451_ = v_isSharedCheck_1487_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1448_);
                                                lean_dec(v___x_1447_);
                                                v___x_1450_ = lean_box(0);
                                                v_isShared_1451_ = v_isSharedCheck_1487_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_e_1379_);
                                            v_a_1488_ = lean_ctor_get(v___x_1447_, 0);
                                            v_isSharedCheck_1495_ =
                                                (!lean_is_exclusive(v___x_1447_)) as u8;
                                            if v_isSharedCheck_1495_ == 0 {
                                                v___x_1490_ = v___x_1447_;
                                                v_isShared_1491_ = v_isSharedCheck_1495_;
                                                state = 11;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1488_);
                                                lean_dec(v___x_1447_);
                                                v___x_1490_ = lean_box(0);
                                                v_isShared_1491_ = v_isSharedCheck_1495_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_1433_);
                                    lean_dec_ref(v_e_1379_);
                                    v_a_1496_ = lean_ctor_get(v___x_1435_, 0);
                                    v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1435_)) as u8;
                                    if v_isSharedCheck_1503_ == 0 {
                                        v___x_1498_ = v___x_1435_;
                                        v_isShared_1499_ = v_isSharedCheck_1503_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1496_);
                                        lean_dec(v___x_1435_);
                                        v___x_1498_ = lean_box(0);
                                        v_isShared_1499_ = v_isSharedCheck_1503_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_1433_);
                                lean_dec_ref(v_e_1379_);
                                v___x_1504_ = lean_box(0);
                                if v_isShared_1425_ == 0 {
                                    lean_ctor_set(v___x_1424_, 0, v___x_1504_);
                                    v___x_1506_ = v___x_1424_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                                    v___x_1506_ = v_reuseFailAlloc_1507_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_1432_);
                            lean_dec(v_parent_x3f_1380_);
                            lean_dec_ref(v_e_1379_);
                            v___x_1508_ = lean_box(0);
                            if v_isShared_1425_ == 0 {
                                lean_ctor_set(v___x_1424_, 0, v___x_1508_);
                                v___x_1510_ = v___x_1424_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
                                v___x_1510_ = v_reuseFailAlloc_1511_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_parent_x3f_1380_);
                        lean_dec_ref(v_e_1379_);
                        v___x_1512_ = lean_box(0);
                        if v_isShared_1425_ == 0 {
                            lean_ctor_set(v___x_1424_, 0, v___x_1512_);
                            v___x_1514_ = v___x_1424_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
                            v___x_1514_ = v_reuseFailAlloc_1515_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_1429_;
            }
            5 => {
                if lean_obj_tag(v_a_1448_) == 1 {
                    lean_del_object(v___x_1450_);
                    v_val_1452_ = lean_ctor_get(v_a_1448_, 0);
                    lean_inc(v_val_1452_);
                    lean_dec_ref_known(v_a_1448_, 1);
                    lean_inc_ref(v_e_1379_);
                    v___x_1453_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
                        v_e_1379_,
                        v_val_1452_,
                        v_a_1381_,
                        v_a_1382_,
                        v_a_1383_,
                        v_a_1384_,
                        v_a_1385_,
                        v_a_1386_,
                        v_a_1387_,
                        v_a_1388_,
                        v_a_1389_,
                        v_a_1390_,
                    );
                    lean_dec(v_val_1452_);
                    if lean_obj_tag(v___x_1453_) == 0 {
                        v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
                        lean_inc(v_a_1454_);
                        lean_dec_ref_known(v___x_1453_, 1);
                        v_options_1455_ = lean_ctor_get(v_a_1389_, 2);
                        v_hasTrace_1456_ = lean_ctor_get_uint8(
                            v_options_1455_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_1456_ == 0 {
                            lean_dec(v_a_1454_);
                            v___y_1409_ = v_a_1381_;
                            v___y_1410_ = v_a_1382_;
                            v___y_1411_ = v_a_1383_;
                            v___y_1412_ = v_a_1384_;
                            v___y_1413_ = v_a_1385_;
                            v___y_1414_ = v_a_1386_;
                            v___y_1415_ = v_a_1387_;
                            v___y_1416_ = v_a_1388_;
                            v___y_1417_ = v_a_1389_;
                            v___y_1418_ = v_a_1390_;
                            state = 2;
                            continue;
                        } else {
                            v_fst_1457_ = lean_ctor_get(v_a_1454_, 0);
                            v_isSharedCheck_1473_ = (!lean_is_exclusive(v_a_1454_)) as u8;
                            if v_isSharedCheck_1473_ == 0 {
                                v_unused_1474_ = lean_ctor_get(v_a_1454_, 1);
                                lean_dec(v_unused_1474_);
                                v___x_1459_ = v_a_1454_;
                                v_isShared_1460_ = v_isSharedCheck_1473_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_fst_1457_);
                                lean_dec(v_a_1454_);
                                v___x_1459_ = lean_box(0);
                                v_isShared_1460_ = v_isSharedCheck_1473_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_1379_);
                        v_a_1475_ = lean_ctor_get(v___x_1453_, 0);
                        v_isSharedCheck_1482_ = (!lean_is_exclusive(v___x_1453_)) as u8;
                        if v_isSharedCheck_1482_ == 0 {
                            v___x_1477_ = v___x_1453_;
                            v_isShared_1478_ = v_isSharedCheck_1482_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1475_);
                            lean_dec(v___x_1453_);
                            v___x_1477_ = lean_box(0);
                            v_isShared_1478_ = v_isSharedCheck_1482_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1448_);
                    lean_dec_ref(v_e_1379_);
                    v___x_1483_ = lean_box(0);
                    if v_isShared_1451_ == 0 {
                        lean_ctor_set(v___x_1450_, 0, v___x_1483_);
                        v___x_1485_ = v___x_1450_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
                        v___x_1485_ = v_reuseFailAlloc_1486_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v_inheritedTraceOptions_1461_ = lean_ctor_get(v_a_1389_, 13);
                v___x_1462_ = l_Lean_Meta_Grind_Arith_Linear_internalize___closed__3;
                v___x_1463_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__6,
                );
                v___x_1464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_1461_,
                    v_options_1455_,
                    v___x_1463_,
                );
                if v___x_1464_ == 0 {
                    lean_del_object(v___x_1459_);
                    lean_dec(v_fst_1457_);
                    v___y_1409_ = v_a_1381_;
                    v___y_1410_ = v_a_1382_;
                    v___y_1411_ = v_a_1383_;
                    v___y_1412_ = v_a_1384_;
                    v___y_1413_ = v_a_1385_;
                    v___y_1414_ = v_a_1386_;
                    v___y_1415_ = v_a_1387_;
                    v___y_1416_ = v_a_1388_;
                    v___y_1417_ = v_a_1389_;
                    v___y_1418_ = v_a_1390_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_e_1379_);
                    v___x_1465_ = l_Lean_MessageData_ofExpr(v_e_1379_);
                    v___x_1466_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_internalize___closed__8,
                    );
                    if v_isShared_1460_ == 0 {
                        lean_ctor_set_tag(v___x_1459_, 7);
                        lean_ctor_set(v___x_1459_, 1, v___x_1466_);
                        lean_ctor_set(v___x_1459_, 0, v___x_1465_);
                        v___x_1468_ = v___x_1459_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1472_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1465_);
                        lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1466_);
                        v___x_1468_ = v_reuseFailAlloc_1472_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1469_ = l_Lean_MessageData_ofExpr(v_fst_1457_);
                v___x_1470_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1470_, 0, v___x_1468_);
                lean_ctor_set(v___x_1470_, 1, v___x_1469_);
                v___x_1471_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(v___x_1462_, v___x_1470_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
                if lean_obj_tag(v___x_1471_) == 0 {
                    lean_dec_ref_known(v___x_1471_, 1);
                    v___y_1409_ = v_a_1381_;
                    v___y_1410_ = v_a_1382_;
                    v___y_1411_ = v_a_1383_;
                    v___y_1412_ = v_a_1384_;
                    v___y_1413_ = v_a_1385_;
                    v___y_1414_ = v_a_1386_;
                    v___y_1415_ = v_a_1387_;
                    v___y_1416_ = v_a_1388_;
                    v___y_1417_ = v_a_1389_;
                    v___y_1418_ = v_a_1390_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_e_1379_);
                    return v___x_1471_;
                }
            }
            8 => {
                if v_isShared_1478_ == 0 {
                    v___x_1480_ = v___x_1477_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
                    v___x_1480_ = v_reuseFailAlloc_1481_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1480_;
            }
            10 => {
                return v___x_1485_;
            }
            11 => {
                if v_isShared_1491_ == 0 {
                    v___x_1493_ = v___x_1490_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1493_;
            }
            13 => {
                if v_isShared_1499_ == 0 {
                    v___x_1501_ = v___x_1498_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1501_;
            }
            15 => {
                return v___x_1506_;
            }
            16 => {
                return v___x_1510_;
            }
            17 => {
                return v___x_1514_;
            }
            18 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(
    mut v_e_1525_: *mut LeanObject,
    mut v_parent_x3f_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
    mut v_a_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1538_: *mut LeanObject = core::ptr::null_mut();
    v_res_1538_ = l_Lean_Meta_Grind_Arith_Linear_internalize(
        v_e_1525_,
        v_parent_x3f_1526_,
        v_a_1527_,
        v_a_1528_,
        v_a_1529_,
        v_a_1530_,
        v_a_1531_,
        v_a_1532_,
        v_a_1533_,
        v_a_1534_,
        v_a_1535_,
        v_a_1536_,
    );
    lean_dec(v_a_1536_);
    lean_dec_ref(v_a_1535_);
    lean_dec(v_a_1534_);
    lean_dec_ref(v_a_1533_);
    lean_dec(v_a_1532_);
    lean_dec_ref(v_a_1531_);
    lean_dec(v_a_1530_);
    lean_dec_ref(v_a_1529_);
    lean_dec(v_a_1528_);
    lean_dec(v_a_1527_);
    return v_res_1538_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(
    mut v_cls_1539_: *mut LeanObject,
    mut v_msg_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
    mut v___y_1542_: *mut LeanObject,
    mut v___y_1543_: *mut LeanObject,
    mut v___y_1544_: *mut LeanObject,
    mut v___y_1545_: *mut LeanObject,
    mut v___y_1546_: *mut LeanObject,
    mut v___y_1547_: *mut LeanObject,
    mut v___y_1548_: *mut LeanObject,
    mut v___y_1549_: *mut LeanObject,
    mut v___y_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1553_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___redArg(
            v_cls_1539_,
            v_msg_1540_,
            v___y_1548_,
            v___y_1549_,
            v___y_1550_,
            v___y_1551_,
        );
    return v___x_1553_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0___boxed(
    mut v_cls_1554_: *mut LeanObject,
    mut v_msg_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1568_: *mut LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__0(
        v_cls_1554_,
        v_msg_1555_,
        v___y_1556_,
        v___y_1557_,
        v___y_1558_,
        v___y_1559_,
        v___y_1560_,
        v___y_1561_,
        v___y_1562_,
        v___y_1563_,
        v___y_1564_,
        v___y_1565_,
        v___y_1566_,
    );
    lean_dec(v___y_1566_);
    lean_dec_ref(v___y_1565_);
    lean_dec(v___y_1564_);
    lean_dec_ref(v___y_1563_);
    lean_dec(v___y_1562_);
    lean_dec_ref(v___y_1561_);
    lean_dec(v___y_1560_);
    lean_dec_ref(v___y_1559_);
    lean_dec(v___y_1558_);
    lean_dec(v___y_1557_);
    lean_dec(v___y_1556_);
    return v_res_1568_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(
    mut v_cls_1569_: *mut LeanObject,
    mut v_msg_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
    mut v___y_1579_: *mut LeanObject,
    mut v___y_1580_: *mut LeanObject,
    mut v___y_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___redArg(
            v_cls_1569_,
            v_msg_1570_,
            v___y_1578_,
            v___y_1579_,
            v___y_1580_,
            v___y_1581_,
        );
    return v___x_1583_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1___boxed(
    mut v_cls_1584_: *mut LeanObject,
    mut v_msg_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_internalize_spec__1(
        v_cls_1584_,
        v_msg_1585_,
        v___y_1586_,
        v___y_1587_,
        v___y_1588_,
        v___y_1589_,
        v___y_1590_,
        v___y_1591_,
        v___y_1592_,
        v___y_1593_,
        v___y_1594_,
        v___y_1595_,
        v___y_1596_,
    );
    lean_dec(v___y_1596_);
    lean_dec_ref(v___y_1595_);
    lean_dec(v___y_1594_);
    lean_dec_ref(v___y_1593_);
    lean_dec(v___y_1592_);
    lean_dec_ref(v___y_1591_);
    lean_dec(v___y_1590_);
    lean_dec_ref(v___y_1589_);
    lean_dec(v___y_1588_);
    lean_dec(v___y_1587_);
    lean_dec(v___y_1586_);
    return v_res_1598_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
}
