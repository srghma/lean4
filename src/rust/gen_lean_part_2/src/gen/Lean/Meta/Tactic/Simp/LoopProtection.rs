// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.LoopProtection
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Linter.Init
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_infer_type, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq, lean_simp, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_usize_add, lean_usize_dec_lt,
    lean_whnf,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_appArg_x21, l_Lean_Expr_hasFVar, l_Lean_mkFVar};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag,
    l_Lean_Linter_linterSetsExt, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_Origin_key, l_Lean_Meta_SimpTheorem_getValue,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, l_Lean_Meta_Simp_SimpM_run___redArg,
    l_Lean_Meta_Simp_UsedSimps_toArray, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [108, 111, 111, 112, 105, 110, 103, 83, 105, 109, 112, 65, 114, 103, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4734170744153359743 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<451> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 451, m_capacity: 451, m_length: 450, m_data: [87, 104, 101, 110, 32, 101, 110, 97, 98, 108, 101, 100, 44, 32, 96, 115, 105, 109, 112, 96, 32, 119, 105, 108, 108, 32, 99, 104, 101, 99, 107, 32, 105, 102, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 112, 97, 115, 115, 101, 100, 32, 97, 115, 32, 115, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 40, 96, 115, 105, 109, 112, 32, 91, 116, 104, 109, 49, 93, 96, 41, 32, 97, 114, 101, 32, 112, 111, 115, 115, 105, 98, 108, 121, 32, 108, 111, 111, 112, 105, 110, 103, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 115, 105, 109, 112, 32, 115, 101, 116, 46, 10, 10, 77, 111, 114, 101, 32, 112, 114, 101, 99, 105, 115, 101, 108, 121, 44, 32, 105, 116, 32, 116, 114, 105, 101, 115, 32, 116, 111, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 110, 100, 32, 99, 111, 109, 112, 108, 97, 105, 110, 115, 32, 105, 102, 32, 116, 104, 97, 116, 32, 102, 97, 105, 108, 115, 44, 32, 119, 104, 105, 99, 104, 32, 105, 116, 32, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 100, 111, 101, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 111, 102, 32, 114, 117, 110, 110, 105, 110, 103, 32, 111, 117, 116, 32, 111, 102, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 114, 101, 108, 97, 116, 105, 118, 101, 108, 121, 32, 101, 120, 112, 101, 110, 115, 105, 118, 101, 32, 99, 104, 101, 99, 107, 44, 32, 115, 111, 32, 105, 116, 32, 105, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 98, 121, 32, 100, 101, 102, 97, 117, 108, 116, 44, 32, 97, 110, 100, 32, 111, 110, 108, 121, 32, 114, 117, 110, 32, 97, 102, 116, 101, 114, 32, 97, 32, 96, 115, 105, 109, 112, 96, 32, 99, 97, 108, 108, 32, 97, 99, 116, 117, 97, 108, 108, 121, 32, 102, 97, 105, 108, 101, 100, 32, 119, 105, 116, 104, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 101, 114, 114, 111, 114, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,492087047182689846 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12613445789975699915 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10068729174000177050 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_linter_loopingSimpArgs: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 147, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 4, m_data: [226, 134, 147, 32, 226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value: leanh::LeanStringObject<95> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 95,
        m_capacity: 95,
        m_length: 94,
        m_data: [
            89, 111, 117, 32, 99, 97, 110, 32, 100, 105, 115, 97, 98, 108, 101, 32, 97, 32, 115,
            105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 114, 111, 109, 32, 116,
            104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 115, 105, 109, 112, 32, 115, 101,
            116, 32, 98, 121, 32, 112, 97, 115, 115, 105, 110, 103, 32, 96, 45, 32, 116, 104, 101,
            111, 114, 101, 109, 78, 97, 109, 101, 96, 32, 116, 111, 32, 96, 115, 105, 109, 112, 96,
            46, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value: leanh::LeanStringObject<33> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            80, 111, 115, 115, 105, 98, 108, 121, 32, 108, 111, 111, 112, 105, 110, 103, 32, 115,
            105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            80, 111, 115, 115, 105, 98, 108, 121, 32, 99, 97, 117, 115, 101, 100, 32, 98, 121, 58,
            32, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100,
        105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111,
        112, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [32, 102, 97, 108, 115, 101, 96, 0],
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        108, 111, 111, 112, 80, 114, 111, 116, 101, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        3981491789317542566 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            11537002108020701424 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 111, 111, 112, 32, 112, 114, 111, 116, 101, 99, 116, 105, 111, 110, 32, 102, 111, 114,
        32, 0,
    ],
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        58, 32, 103, 111, 116, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(
    mut v_name_1441_: *mut leanh::LeanObject,
    mut v_decl_1442_: *mut leanh::LeanObject,
    mut v_ref_1443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut v_unused_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1445_ = leanh::lean_ctor_get(v_decl_1442_, 0);
                v_descr_1446_ = leanh::lean_ctor_get(v_decl_1442_, 1);
                v_deprecation_x3f_1447_ = leanh::lean_ctor_get(v_decl_1442_, 2);
                v___x_1448_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1449_ = (leanh::lean_unbox(v_defValue_1445_) as u8);
                leanh::lean_ctor_set_uint8(v___x_1448_, 0 as u32, v___x_1449_);
                leanh::lean_inc(v_deprecation_x3f_1447_);
                leanh::lean_inc_ref(v_descr_1446_);
                leanh::lean_inc_n(v_name_1441_, 2);
                v___x_1450_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1450_, 0, v_name_1441_);
                leanh::lean_ctor_set(v___x_1450_, 1, v_ref_1443_);
                leanh::lean_ctor_set(v___x_1450_, 2, v___x_1448_);
                leanh::lean_ctor_set(v___x_1450_, 3, v_descr_1446_);
                leanh::lean_ctor_set(v___x_1450_, 4, v_deprecation_x3f_1447_);
                v___x_1451_ = lean_register_option(v_name_1441_, v___x_1450_);
                if leanh::lean_obj_tag(v___x_1451_) == 0 {
                    v_isSharedCheck_1459_ = (!leanh::lean_is_exclusive(v___x_1451_)) as u8;
                    if v_isSharedCheck_1459_ == 0 {
                        v_unused_1460_ = leanh::lean_ctor_get(v___x_1451_, 0);
                        leanh::lean_dec(v_unused_1460_);
                        v___x_1453_ = v___x_1451_;
                        v_isShared_1454_ = v_isSharedCheck_1459_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1451_);
                        v___x_1453_ = leanh::lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1459_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_1441_);
                    v_a_1461_ = leanh::lean_ctor_get(v___x_1451_, 0);
                    v_isSharedCheck_1468_ = (!leanh::lean_is_exclusive(v___x_1451_)) as u8;
                    if v_isSharedCheck_1468_ == 0 {
                        v___x_1463_ = v___x_1451_;
                        v_isShared_1464_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1461_);
                        leanh::lean_dec(v___x_1451_);
                        v___x_1463_ = leanh::lean_box(0);
                        v_isShared_1464_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_1445_);
                v___x_1455_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1455_, 0, v_name_1441_);
                leanh::lean_ctor_set(v___x_1455_, 1, v_defValue_1445_);
                if v_isShared_1454_ == 0 {
                    leanh::lean_ctor_set(v___x_1453_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
                    v___x_1457_ = v_reuseFailAlloc_1458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1457_;
            }
            3 => {
                if v_isShared_1464_ == 0 {
                    v___x_1466_ = v___x_1463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1469_: *mut leanh::LeanObject,
    mut v_decl_1470_: *mut leanh::LeanObject,
    mut v_ref_1471_: *mut leanh::LeanObject,
    mut v_a_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_1469_, v_decl_1470_, v_ref_1471_);
    leanh::lean_dec_ref(v_decl_1470_);
    return v_res_1473_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1496_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1497_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1498_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v___x_1495_, v___x_1496_, v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(
    mut v_a_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
    return v_res_1500_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
    mut v_a_1501_: *mut leanh::LeanObject,
    mut v_usedTheorems_1502_: *mut leanh::LeanObject,
    mut v_a_x3f_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_unused_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_st_ref_take(v_a_1501_);
                v_cache_1506_ = leanh::lean_ctor_get(v___x_1505_, 0);
                v_congrCache_1507_ = leanh::lean_ctor_get(v___x_1505_, 1);
                v_dsimpCache_1508_ = leanh::lean_ctor_get(v___x_1505_, 2);
                v_numSteps_1509_ = leanh::lean_ctor_get(v___x_1505_, 4);
                v_diag_1510_ = leanh::lean_ctor_get(v___x_1505_, 5);
                v_isSharedCheck_1520_ = (!leanh::lean_is_exclusive(v___x_1505_)) as u8;
                if v_isSharedCheck_1520_ == 0 {
                    v_unused_1521_ = leanh::lean_ctor_get(v___x_1505_, 3);
                    leanh::lean_dec(v_unused_1521_);
                    v___x_1512_ = v___x_1505_;
                    v_isShared_1513_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1510_);
                    leanh::lean_inc(v_numSteps_1509_);
                    leanh::lean_inc(v_dsimpCache_1508_);
                    leanh::lean_inc(v_congrCache_1507_);
                    leanh::lean_inc(v_cache_1506_);
                    leanh::lean_dec(v___x_1505_);
                    v___x_1512_ = leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1513_ == 0 {
                    leanh::lean_ctor_set(v___x_1512_, 3, v_usedTheorems_1502_);
                    v___x_1515_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_cache_1506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_congrCache_1507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_dsimpCache_1508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_usedTheorems_1502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_numSteps_1509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_diag_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1516_ = lean_st_ref_set(v_a_1501_, v___x_1515_);
                v___x_1517_ = leanh::lean_box(0);
                v___x_1518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_usedTheorems_1523_: *mut leanh::LeanObject,
    mut v_a_x3f_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
        v_a_1522_,
        v_usedTheorems_1523_,
        v_a_x3f_1524_,
    );
    leanh::lean_dec(v_a_x3f_1524_);
    leanh::lean_dec(v_a_1522_);
    return v_res_1526_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1527_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once),
        _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0,
    );
    v___x_1529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1529_, 0, v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = leanh::lean_unsigned_to_nat(0);
    v___x_1531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once),
        _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1,
    );
    v___x_1532_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
    leanh::lean_ctor_set(v___x_1532_, 1, v___x_1530_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(
    mut v_x_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
    mut v_a_1537_: *mut leanh::LeanObject,
    mut v_a_1538_: *mut leanh::LeanObject,
    mut v_a_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_unused_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut v_unused_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1542_ = lean_st_ref_get(v_a_1536_);
                v___x_1543_ = lean_st_ref_take(v_a_1536_);
                v_cache_1544_ = leanh::lean_ctor_get(v___x_1543_, 0);
                v_congrCache_1545_ = leanh::lean_ctor_get(v___x_1543_, 1);
                v_dsimpCache_1546_ = leanh::lean_ctor_get(v___x_1543_, 2);
                v_numSteps_1547_ = leanh::lean_ctor_get(v___x_1543_, 4);
                v_diag_1548_ = leanh::lean_ctor_get(v___x_1543_, 5);
                v_isSharedCheck_1587_ = (!leanh::lean_is_exclusive(v___x_1543_)) as u8;
                if v_isSharedCheck_1587_ == 0 {
                    v_unused_1588_ = leanh::lean_ctor_get(v___x_1543_, 3);
                    leanh::lean_dec(v_unused_1588_);
                    v___x_1550_ = v___x_1543_;
                    v_isShared_1551_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1548_);
                    leanh::lean_inc(v_numSteps_1547_);
                    leanh::lean_inc(v_dsimpCache_1546_);
                    leanh::lean_inc(v_congrCache_1545_);
                    leanh::lean_inc(v_cache_1544_);
                    leanh::lean_dec(v___x_1543_);
                    v___x_1550_ = leanh::lean_box(0);
                    v_isShared_1551_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1552_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2,
                );
                if v_isShared_1551_ == 0 {
                    leanh::lean_ctor_set(v___x_1550_, 3, v___x_1552_);
                    v___x_1554_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_cache_1544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_congrCache_1545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_dsimpCache_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 3, v___x_1552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_numSteps_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_diag_1548_);
                    v___x_1554_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1555_ = lean_st_ref_set(v_a_1536_, v___x_1554_);
                v_usedTheorems_1556_ = leanh::lean_ctor_get(v___x_1542_, 3);
                leanh::lean_inc_ref(v_usedTheorems_1556_);
                leanh::lean_dec(v___x_1542_);
                leanh::lean_inc(v_a_1540_);
                leanh::lean_inc_ref(v_a_1539_);
                leanh::lean_inc(v_a_1538_);
                leanh::lean_inc_ref(v_a_1537_);
                leanh::lean_inc(v_a_1536_);
                leanh::lean_inc_ref(v_a_1535_);
                leanh::lean_inc(v_a_1534_);
                v_r_1557_ = leanh::lean_apply_8(
                    v_x_1533_,
                    v_a_1534_,
                    v_a_1535_,
                    v_a_1536_,
                    v_a_1537_,
                    v_a_1538_,
                    v_a_1539_,
                    v_a_1540_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1557_) == 0 {
                    v_a_1558_ = leanh::lean_ctor_get(v_r_1557_, 0);
                    v_isSharedCheck_1574_ = (!leanh::lean_is_exclusive(v_r_1557_)) as u8;
                    if v_isSharedCheck_1574_ == 0 {
                        v___x_1560_ = v_r_1557_;
                        v_isShared_1561_ = v_isSharedCheck_1574_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1558_);
                        leanh::lean_dec(v_r_1557_);
                        v___x_1560_ = leanh::lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1574_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1575_ = leanh::lean_ctor_get(v_r_1557_, 0);
                    leanh::lean_inc(v_a_1575_);
                    leanh::lean_dec_ref_known(v_r_1557_, 1);
                    v___x_1576_ = leanh::lean_box(0);
                    v___x_1577_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                        v_a_1536_,
                        v_usedTheorems_1556_,
                        v___x_1576_,
                    );
                    v_isSharedCheck_1584_ = (!leanh::lean_is_exclusive(v___x_1577_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v_unused_1585_ = leanh::lean_ctor_get(v___x_1577_, 0);
                        leanh::lean_dec(v_unused_1585_);
                        v___x_1579_ = v___x_1577_;
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1577_);
                        v___x_1579_ = leanh::lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_1558_);
                if v_isShared_1561_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1560_, 1);
                    v___x_1563_ = v___x_1560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1564_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                    v_a_1536_,
                    v_usedTheorems_1556_,
                    v___x_1563_,
                );
                leanh::lean_dec_ref(v___x_1563_);
                v_isSharedCheck_1571_ = (!leanh::lean_is_exclusive(v___x_1564_)) as u8;
                if v_isSharedCheck_1571_ == 0 {
                    v_unused_1572_ = leanh::lean_ctor_get(v___x_1564_, 0);
                    leanh::lean_dec(v_unused_1572_);
                    v___x_1566_ = v___x_1564_;
                    v_isShared_1567_ = v_isSharedCheck_1571_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1564_);
                    v___x_1566_ = leanh::lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1567_ == 0 {
                    leanh::lean_ctor_set(v___x_1566_, 0, v_a_1558_);
                    v___x_1569_ = v___x_1566_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1558_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1569_;
            }
            7 => {
                if v_isShared_1580_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1579_, 1);
                    leanh::lean_ctor_set(v___x_1579_, 0, v_a_1575_);
                    v___x_1582_ = v___x_1579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1575_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___boxed(
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_a_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
    mut v_a_1592_: *mut leanh::LeanObject,
    mut v_a_1593_: *mut leanh::LeanObject,
    mut v_a_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(
        v_x_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_,
    );
    leanh::lean_dec(v_a_1596_);
    leanh::lean_dec_ref(v_a_1595_);
    leanh::lean_dec(v_a_1594_);
    leanh::lean_dec_ref(v_a_1593_);
    leanh::lean_dec(v_a_1592_);
    leanh::lean_dec_ref(v_a_1591_);
    leanh::lean_dec(v_a_1590_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems(
    mut v_00_u03b1_1599_: *mut leanh::LeanObject,
    mut v_x_1600_: *mut leanh::LeanObject,
    mut v_a_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
    mut v_a_1605_: *mut leanh::LeanObject,
    mut v_a_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_unused_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_unused_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v_unused_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = lean_st_ref_get(v_a_1603_);
                v___x_1610_ = lean_st_ref_take(v_a_1603_);
                v_cache_1611_ = leanh::lean_ctor_get(v___x_1610_, 0);
                v_congrCache_1612_ = leanh::lean_ctor_get(v___x_1610_, 1);
                v_dsimpCache_1613_ = leanh::lean_ctor_get(v___x_1610_, 2);
                v_numSteps_1614_ = leanh::lean_ctor_get(v___x_1610_, 4);
                v_diag_1615_ = leanh::lean_ctor_get(v___x_1610_, 5);
                v_isSharedCheck_1654_ = (!leanh::lean_is_exclusive(v___x_1610_)) as u8;
                if v_isSharedCheck_1654_ == 0 {
                    v_unused_1655_ = leanh::lean_ctor_get(v___x_1610_, 3);
                    leanh::lean_dec(v_unused_1655_);
                    v___x_1617_ = v___x_1610_;
                    v_isShared_1618_ = v_isSharedCheck_1654_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1615_);
                    leanh::lean_inc(v_numSteps_1614_);
                    leanh::lean_inc(v_dsimpCache_1613_);
                    leanh::lean_inc(v_congrCache_1612_);
                    leanh::lean_inc(v_cache_1611_);
                    leanh::lean_dec(v___x_1610_);
                    v___x_1617_ = leanh::lean_box(0);
                    v_isShared_1618_ = v_isSharedCheck_1654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1619_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2,
                );
                if v_isShared_1618_ == 0 {
                    leanh::lean_ctor_set(v___x_1617_, 3, v___x_1619_);
                    v___x_1621_ = v___x_1617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_cache_1611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_congrCache_1612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_dsimpCache_1613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___x_1619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_numSteps_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 5, v_diag_1615_);
                    v___x_1621_ = v_reuseFailAlloc_1653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1622_ = lean_st_ref_set(v_a_1603_, v___x_1621_);
                v_usedTheorems_1623_ = leanh::lean_ctor_get(v___x_1609_, 3);
                leanh::lean_inc_ref(v_usedTheorems_1623_);
                leanh::lean_dec(v___x_1609_);
                leanh::lean_inc(v_a_1607_);
                leanh::lean_inc_ref(v_a_1606_);
                leanh::lean_inc(v_a_1605_);
                leanh::lean_inc_ref(v_a_1604_);
                leanh::lean_inc(v_a_1603_);
                leanh::lean_inc_ref(v_a_1602_);
                leanh::lean_inc(v_a_1601_);
                v_r_1624_ = leanh::lean_apply_8(
                    v_x_1600_,
                    v_a_1601_,
                    v_a_1602_,
                    v_a_1603_,
                    v_a_1604_,
                    v_a_1605_,
                    v_a_1606_,
                    v_a_1607_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1624_) == 0 {
                    v_a_1625_ = leanh::lean_ctor_get(v_r_1624_, 0);
                    v_isSharedCheck_1641_ = (!leanh::lean_is_exclusive(v_r_1624_)) as u8;
                    if v_isSharedCheck_1641_ == 0 {
                        v___x_1627_ = v_r_1624_;
                        v_isShared_1628_ = v_isSharedCheck_1641_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1625_);
                        leanh::lean_dec(v_r_1624_);
                        v___x_1627_ = leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1641_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1642_ = leanh::lean_ctor_get(v_r_1624_, 0);
                    leanh::lean_inc(v_a_1642_);
                    leanh::lean_dec_ref_known(v_r_1624_, 1);
                    v___x_1643_ = leanh::lean_box(0);
                    v___x_1644_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                        v_a_1603_,
                        v_usedTheorems_1623_,
                        v___x_1643_,
                    );
                    v_isSharedCheck_1651_ = (!leanh::lean_is_exclusive(v___x_1644_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v_unused_1652_ = leanh::lean_ctor_get(v___x_1644_, 0);
                        leanh::lean_dec(v_unused_1652_);
                        v___x_1646_ = v___x_1644_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1644_);
                        v___x_1646_ = leanh::lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_1625_);
                if v_isShared_1628_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1627_, 1);
                    v___x_1630_ = v___x_1627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1625_);
                    v___x_1630_ = v_reuseFailAlloc_1640_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1631_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                    v_a_1603_,
                    v_usedTheorems_1623_,
                    v___x_1630_,
                );
                leanh::lean_dec_ref(v___x_1630_);
                v_isSharedCheck_1638_ = (!leanh::lean_is_exclusive(v___x_1631_)) as u8;
                if v_isSharedCheck_1638_ == 0 {
                    v_unused_1639_ = leanh::lean_ctor_get(v___x_1631_, 0);
                    leanh::lean_dec(v_unused_1639_);
                    v___x_1633_ = v___x_1631_;
                    v_isShared_1634_ = v_isSharedCheck_1638_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1631_);
                    v___x_1633_ = leanh::lean_box(0);
                    v_isShared_1634_ = v_isSharedCheck_1638_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1634_ == 0 {
                    leanh::lean_ctor_set(v___x_1633_, 0, v_a_1625_);
                    v___x_1636_ = v___x_1633_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1625_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1636_;
            }
            7 => {
                if v_isShared_1647_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1646_, 1);
                    leanh::lean_ctor_set(v___x_1646_, 0, v_a_1642_);
                    v___x_1649_ = v___x_1646_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1642_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(
    mut v_00_u03b1_1656_: *mut leanh::LeanObject,
    mut v_x_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
    mut v_a_1662_: *mut leanh::LeanObject,
    mut v_a_1663_: *mut leanh::LeanObject,
    mut v_a_1664_: *mut leanh::LeanObject,
    mut v_a_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_Meta_Simp_withFreshUsedTheorems(
        v_00_u03b1_1656_,
        v_x_1657_,
        v_a_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
        v_a_1663_,
        v_a_1664_,
    );
    leanh::lean_dec(v_a_1664_);
    leanh::lean_dec_ref(v_a_1663_);
    leanh::lean_dec(v_a_1662_);
    leanh::lean_dec_ref(v_a_1661_);
    leanh::lean_dec(v_a_1660_);
    leanh::lean_dec_ref(v_a_1659_);
    leanh::lean_dec(v_a_1658_);
    return v_res_1666_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0;
    v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2;
    v___x_1672_ = l_Lean_stringToMessageData(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4;
    v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_1679_: u8 = 0;
    let mut v_inv_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v_r_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut v_ref_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1676_) {
                0 => {
                    v_declName_1678_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc(v_declName_1678_);
                    v_post_1679_ = leanh::lean_ctor_get_uint8(
                        v_x_1676_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_inv_1680_ = leanh::lean_ctor_get_uint8(
                        v_x_1676_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1681_ = 0;
                    v_r_1682_ = l_Lean_MessageData_ofConstName(v_declName_1678_, v___x_1681_);
                    if v_post_1679_ == 0 {
                        if v_inv_1680_ == 0 {
                            v___x_1683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
                            v___x_1684_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                            leanh::lean_ctor_set(v___x_1684_, 1, v_r_1682_);
                            v___x_1685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1685_, 0, v___x_1684_);
                            return v___x_1685_;
                        } else {
                            v___x_1686_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
                            v___x_1687_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
                            leanh::lean_ctor_set(v___x_1687_, 1, v_r_1682_);
                            v___x_1688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1688_, 0, v___x_1687_);
                            return v___x_1688_;
                        }
                    } else {
                        if v_inv_1680_ == 0 {
                            v___x_1689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1689_, 0, v_r_1682_);
                            return v___x_1689_;
                        } else {
                            v___x_1690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
                            v___x_1691_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
                            leanh::lean_ctor_set(v___x_1691_, 1, v_r_1682_);
                            v___x_1692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                            return v___x_1692_;
                        }
                    }
                }
                1 => {
                    v_fvarId_1693_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    v_isSharedCheck_1702_ = (!leanh::lean_is_exclusive(v_x_1676_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1695_ = v_x_1676_;
                        v_isShared_1696_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_1693_);
                        leanh::lean_dec(v_x_1676_);
                        v___x_1695_ = leanh::lean_box(0);
                        v_isShared_1696_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ref_1703_ = leanh::lean_ctor_get(v_x_1676_, 1);
                    leanh::lean_inc(v_ref_1703_);
                    leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1704_ = l_Lean_MessageData_ofSyntax(v_ref_1703_);
                    v___x_1705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1705_, 0, v___x_1704_);
                    return v___x_1705_;
                }
                _ => {
                    v_name_1706_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    v_isSharedCheck_1714_ = (!leanh::lean_is_exclusive(v_x_1676_)) as u8;
                    if v_isSharedCheck_1714_ == 0 {
                        v___x_1708_ = v_x_1676_;
                        v_isShared_1709_ = v_isSharedCheck_1714_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_1706_);
                        leanh::lean_dec(v_x_1676_);
                        v___x_1708_ = leanh::lean_box(0);
                        v_isShared_1709_ = v_isSharedCheck_1714_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1697_ = l_Lean_mkFVar(v_fvarId_1693_);
                v___x_1698_ = l_Lean_MessageData_ofExpr(v___x_1697_);
                if v_isShared_1696_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1695_, 0);
                    leanh::lean_ctor_set(v___x_1695_, 0, v___x_1698_);
                    v___x_1700_ = v___x_1695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1700_;
            }
            3 => {
                v___x_1710_ = l_Lean_MessageData_ofName(v_name_1706_);
                if v_isShared_1709_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1708_, 0);
                    leanh::lean_ctor_set(v___x_1708_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(
    mut v_x_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_1715_);
    return v_res_1717_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(
    mut v_x_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
    mut v___y_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_1718_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(
    mut v_x_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
    leanh::lean_dec(v___y_1729_);
    leanh::lean_dec_ref(v___y_1728_);
    leanh::lean_dec(v___y_1727_);
    leanh::lean_dec_ref(v___y_1726_);
    return v_res_1731_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0;
    v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
    return v___x_1734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(
    mut v_sz_1735_: usize,
    mut v_i_1736_: usize,
    mut v_bs_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: usize = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1743_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
                if v___x_1743_ == 0 {
                    v___x_1744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1744_, 0, v_bs_1737_);
                    return v___x_1744_;
                } else {
                    v_v_1745_ = lean_array_uget(v_bs_1737_, v_i_1736_);
                    v___x_1746_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1747_ = lean_array_uset(v_bs_1737_, v_i_1736_, v___x_1746_);
                    v___x_1754_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_v_1745_);
                    if leanh::lean_obj_tag(v___x_1754_) == 0 {
                        v_a_1755_ = leanh::lean_ctor_get(v___x_1754_, 0);
                        leanh::lean_inc(v_a_1755_);
                        leanh::lean_dec_ref_known(v___x_1754_, 1);
                        v___x_1756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
                        v___x_1757_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                        leanh::lean_ctor_set(v___x_1757_, 1, v_a_1755_);
                        v___x_1758_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1758_, 0, v___x_1757_);
                        leanh::lean_ctor_set(v___x_1758_, 1, v___x_1756_);
                        v_a_1749_ = v___x_1758_;
                        state = 1;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v___x_1754_) == 0 {
                            v_a_1759_ = leanh::lean_ctor_get(v___x_1754_, 0);
                            leanh::lean_inc(v_a_1759_);
                            leanh::lean_dec_ref_known(v___x_1754_, 1);
                            v_a_1749_ = v_a_1759_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1747_);
                            v_a_1760_ = leanh::lean_ctor_get(v___x_1754_, 0);
                            v_isSharedCheck_1767_ =
                                (!leanh::lean_is_exclusive(v___x_1754_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v___x_1762_ = v___x_1754_;
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1760_);
                                leanh::lean_dec(v___x_1754_);
                                v___x_1762_ = leanh::lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1750_ = 1usize;
                v___x_1751_ = lean_usize_add(v_i_1736_, v___x_1750_);
                v___x_1752_ = lean_array_uset(v_bs_x27_1747_, v_i_1736_, v_a_1749_);
                v_i_1736_ = v___x_1751_;
                v_bs_1737_ = v___x_1752_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1763_ == 0 {
                    v___x_1765_ = v___x_1762_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(
    mut v_sz_1768_: *mut leanh::LeanObject,
    mut v_i_1769_: *mut leanh::LeanObject,
    mut v_bs_1770_: *mut leanh::LeanObject,
    mut v___y_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1776_: usize = 0;
    let mut v_i_boxed_1777_: usize = 0;
    let mut v_res_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1776_ = leanh::lean_unbox_usize(v_sz_1768_);
    leanh::lean_dec(v_sz_1768_);
    v_i_boxed_1777_ = leanh::lean_unbox_usize(v_i_1769_);
    leanh::lean_dec(v_i_1769_);
    v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_boxed_1776_, v_i_boxed_1777_, v_bs_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
    leanh::lean_dec(v___y_1774_);
    leanh::lean_dec_ref(v___y_1773_);
    leanh::lean_dec(v___y_1772_);
    leanh::lean_dec_ref(v___y_1771_);
    return v_res_1778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(
    mut v_origins_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
    mut v_a_1781_: *mut leanh::LeanObject,
    mut v_a_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_a_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1785_ = lean_array_size(v_origins_1779_);
                v___x_1786_ = 0usize;
                v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_1785_, v___x_1786_, v_origins_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
                if leanh::lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1797_ = (!leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1790_ = v___x_1787_;
                        v_isShared_1791_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1788_);
                        leanh::lean_dec(v___x_1787_);
                        v___x_1790_ = leanh::lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1798_ = leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1805_ = (!leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v___x_1800_ = v___x_1787_;
                        v_isShared_1801_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1798_);
                        leanh::lean_dec(v___x_1787_);
                        v___x_1800_ = leanh::lean_box(0);
                        v_isShared_1801_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1792_ = lean_array_to_list(v_a_1788_);
                v___x_1793_ = l_Lean_MessageData_andList(v___x_1792_);
                if v_isShared_1791_ == 0 {
                    leanh::lean_ctor_set(v___x_1790_, 0, v___x_1793_);
                    v___x_1795_ = v___x_1790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1795_;
            }
            3 => {
                if v_isShared_1801_ == 0 {
                    v___x_1803_ = v___x_1800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(
    mut v_origins_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
    mut v_a_1809_: *mut leanh::LeanObject,
    mut v_a_1810_: *mut leanh::LeanObject,
    mut v_a_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(
        v_origins_1806_,
        v_a_1807_,
        v_a_1808_,
        v_a_1809_,
        v_a_1810_,
    );
    leanh::lean_dec(v_a_1810_);
    leanh::lean_dec_ref(v_a_1809_);
    leanh::lean_dec(v_a_1808_);
    leanh::lean_dec_ref(v_a_1807_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(
    mut v_x_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_1816_: u8 = 0;
    let mut v_inv_1817_: u8 = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v_r_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_ref_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1813_) {
                0 => {
                    v_declName_1815_ = leanh::lean_ctor_get(v_x_1813_, 0);
                    leanh::lean_inc(v_declName_1815_);
                    v_post_1816_ = leanh::lean_ctor_get_uint8(
                        v_x_1813_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_inv_1817_ = leanh::lean_ctor_get_uint8(
                        v_x_1813_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1813_, 1);
                    v___x_1818_ = 0;
                    v_r_1819_ = l_Lean_MessageData_ofConstName(v_declName_1815_, v___x_1818_);
                    if v_post_1816_ == 0 {
                        if v_inv_1817_ == 0 {
                            v___x_1820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
                            v___x_1821_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                            leanh::lean_ctor_set(v___x_1821_, 1, v_r_1819_);
                            v___x_1822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1822_, 0, v___x_1821_);
                            return v___x_1822_;
                        } else {
                            v___x_1823_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
                            v___x_1824_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
                            leanh::lean_ctor_set(v___x_1824_, 1, v_r_1819_);
                            v___x_1825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1825_, 0, v___x_1824_);
                            return v___x_1825_;
                        }
                    } else {
                        if v_inv_1817_ == 0 {
                            v___x_1826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1826_, 0, v_r_1819_);
                            return v___x_1826_;
                        } else {
                            v___x_1827_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
                            v___x_1828_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1828_, 0, v___x_1827_);
                            leanh::lean_ctor_set(v___x_1828_, 1, v_r_1819_);
                            v___x_1829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1829_, 0, v___x_1828_);
                            return v___x_1829_;
                        }
                    }
                }
                1 => {
                    v_fvarId_1830_ = leanh::lean_ctor_get(v_x_1813_, 0);
                    v_isSharedCheck_1839_ = (!leanh::lean_is_exclusive(v_x_1813_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1832_ = v_x_1813_;
                        v_isShared_1833_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_1830_);
                        leanh::lean_dec(v_x_1813_);
                        v___x_1832_ = leanh::lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ref_1840_ = leanh::lean_ctor_get(v_x_1813_, 1);
                    leanh::lean_inc(v_ref_1840_);
                    leanh::lean_dec_ref_known(v_x_1813_, 2);
                    v___x_1841_ = l_Lean_MessageData_ofSyntax(v_ref_1840_);
                    v___x_1842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
                    return v___x_1842_;
                }
                _ => {
                    v_name_1843_ = leanh::lean_ctor_get(v_x_1813_, 0);
                    v_isSharedCheck_1851_ = (!leanh::lean_is_exclusive(v_x_1813_)) as u8;
                    if v_isSharedCheck_1851_ == 0 {
                        v___x_1845_ = v_x_1813_;
                        v_isShared_1846_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_1843_);
                        leanh::lean_dec(v_x_1813_);
                        v___x_1845_ = leanh::lean_box(0);
                        v_isShared_1846_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1834_ = l_Lean_mkFVar(v_fvarId_1830_);
                v___x_1835_ = l_Lean_MessageData_ofExpr(v___x_1834_);
                if v_isShared_1833_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1832_, 0);
                    leanh::lean_ctor_set(v___x_1832_, 0, v___x_1835_);
                    v___x_1837_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1837_;
            }
            3 => {
                v___x_1847_ = l_Lean_MessageData_ofName(v_name_1843_);
                if v_isShared_1846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1845_, 0);
                    leanh::lean_ctor_set(v___x_1845_, 0, v___x_1847_);
                    v___x_1849_ = v___x_1845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(
    mut v_x_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ =
        l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_1852_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(
    mut v_x_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ =
        l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_1855_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(
    mut v_x_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
    mut v___y_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(
        v_x_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
        v___y_1869_,
        v___y_1870_,
        v___y_1871_,
        v___y_1872_,
    );
    leanh::lean_dec(v___y_1872_);
    leanh::lean_dec_ref(v___y_1871_);
    leanh::lean_dec(v___y_1870_);
    leanh::lean_dec_ref(v___y_1869_);
    leanh::lean_dec(v___y_1868_);
    leanh::lean_dec_ref(v___y_1867_);
    leanh::lean_dec(v___y_1866_);
    return v_res_1874_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(
    mut v___x_1875_: *mut leanh::LeanObject,
    mut v_as_1876_: *mut leanh::LeanObject,
    mut v_sz_1877_: usize,
    mut v_i_1878_: usize,
    mut v_b_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: usize = 0;
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: u8 = 0;
    let mut v_declName_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inv_1894_: u8 = 0;
    let mut v_declName_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inv_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1886_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
                if v___x_1886_ == 0 {
                    v___x_1887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1887_, 0, v_b_1879_);
                    return v___x_1887_;
                } else {
                    v_a_1888_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
                    if leanh::lean_obj_tag(v_a_1888_) == 0 {
                        if leanh::lean_obj_tag(v___x_1875_) == 0 {
                            v_declName_1893_ = leanh::lean_ctor_get(v_a_1888_, 0);
                            v_inv_1894_ = leanh::lean_ctor_get_uint8(
                                v_a_1888_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1)
                                    as u32,
                            );
                            v_declName_1895_ = leanh::lean_ctor_get(v___x_1875_, 0);
                            v_inv_1896_ = leanh::lean_ctor_get_uint8(
                                v___x_1875_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1)
                                    as u32,
                            );
                            v___x_1897_ = lean_name_eq(v_declName_1893_, v_declName_1895_);
                            if v___x_1897_ == 0 {
                                v___y_1892_ = v___x_1897_;
                                state = 3;
                                continue;
                            } else {
                                if v_inv_1894_ == 0 {
                                    if v_inv_1896_ == 0 {
                                        v___y_1892_ = v___x_1897_;
                                        state = 3;
                                        continue;
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1892_ = v_inv_1896_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1875_) == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_1898_ = l_Lean_Meta_Origin_key(v_a_1888_);
                            v___x_1899_ = l_Lean_Meta_Origin_key(v___x_1875_);
                            v___x_1900_ = lean_name_eq(v___x_1898_, v___x_1899_);
                            leanh::lean_dec(v___x_1899_);
                            leanh::lean_dec(v___x_1898_);
                            v___y_1892_ = v___x_1900_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1883_ = 1usize;
                v___x_1884_ = lean_usize_add(v_i_1878_, v___x_1883_);
                v_i_1878_ = v___x_1884_;
                v_b_1879_ = v_a_1882_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_a_1888_);
                v___x_1890_ = lean_array_push(v_b_1879_, v_a_1888_);
                v_a_1882_ = v___x_1890_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_1892_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v_a_1882_ = v_b_1879_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(
    mut v___x_1901_: *mut leanh::LeanObject,
    mut v_as_1902_: *mut leanh::LeanObject,
    mut v_sz_1903_: *mut leanh::LeanObject,
    mut v_i_1904_: *mut leanh::LeanObject,
    mut v_b_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1907_: usize = 0;
    let mut v_i_boxed_1908_: usize = 0;
    let mut v_res_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1907_ = leanh::lean_unbox_usize(v_sz_1903_);
    leanh::lean_dec(v_sz_1903_);
    v_i_boxed_1908_ = leanh::lean_unbox_usize(v_i_1904_);
    leanh::lean_dec(v_i_1904_);
    v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_1901_, v_as_1902_, v_sz_boxed_1907_, v_i_boxed_1908_, v_b_1905_);
    leanh::lean_dec_ref(v_as_1902_);
    leanh::lean_dec_ref(v___x_1901_);
    return v_res_1909_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0;
    v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once),
        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1,
    );
    v___x_1914_ = l_Lean_MessageData_hint_x27(v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1918_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
    v_msg_1919_ = l_Lean_stringToMessageData(v___x_1918_);
    return v_msg_1919_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6;
    v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8;
    v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn l_Lean_Meta_Simp_mkLoopWarningMsg(
    mut v_thm_1926_: *mut leanh::LeanObject,
    mut v_a_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_a_1931_: *mut leanh::LeanObject,
    mut v_a_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_msg_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1948_: usize = 0;
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_origin_1940_ = leanh::lean_ctor_get(v_thm_1926_, 4);
                leanh::lean_inc_ref_n(v_origin_1940_, 2);
                leanh::lean_dec_ref(v_thm_1926_);
                v___x_1941_ =
                    l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(
                        v_origin_1940_,
                    );
                v_a_1942_ = leanh::lean_ctor_get(v___x_1941_, 0);
                leanh::lean_inc(v_a_1942_);
                leanh::lean_dec_ref(v___x_1941_);
                v___x_1943_ = lean_st_ref_get(v_a_1929_);
                v_usedTheorems_1944_ = leanh::lean_ctor_get(v___x_1943_, 3);
                leanh::lean_inc_ref(v_usedTheorems_1944_);
                leanh::lean_dec(v___x_1943_);
                v___x_1945_ = leanh::lean_unsigned_to_nat(0);
                v___x_1946_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3;
                v___x_1947_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_1944_);
                leanh::lean_dec_ref(v_usedTheorems_1944_);
                v_sz_1948_ = lean_array_size(v___x_1947_);
                v___x_1949_ = 0usize;
                v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_1940_, v___x_1947_, v_sz_1948_, v___x_1949_, v___x_1946_);
                leanh::lean_dec_ref(v___x_1947_);
                leanh::lean_dec_ref(v_origin_1940_);
                if leanh::lean_obj_tag(v___x_1950_) == 0 {
                    v_a_1951_ = leanh::lean_ctor_get(v___x_1950_, 0);
                    leanh::lean_inc(v_a_1951_);
                    leanh::lean_dec_ref_known(v___x_1950_, 1);
                    v_msg_1952_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once),
                        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5,
                    );
                    v___x_1953_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once),
                        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7,
                    );
                    v___x_1954_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                    leanh::lean_ctor_set(v___x_1954_, 1, v_a_1942_);
                    v___x_1955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
                    v___x_1956_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1956_, 0, v___x_1954_);
                    leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
                    v___x_1957_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1957_, 0, v_msg_1952_);
                    leanh::lean_ctor_set(v___x_1957_, 1, v___x_1956_);
                    v___x_1958_ = lean_array_get_size(v_a_1951_);
                    v___x_1959_ = lean_nat_dec_eq(v___x_1958_, v___x_1945_);
                    if v___x_1959_ == 0 {
                        v___x_1960_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_1951_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
                        if leanh::lean_obj_tag(v___x_1960_) == 0 {
                            v_a_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
                            leanh::lean_inc(v_a_1961_);
                            leanh::lean_dec_ref_known(v___x_1960_, 1);
                            v___x_1962_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once
                                ),
                                _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9,
                            );
                            v___x_1963_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                            leanh::lean_ctor_set(v___x_1963_, 1, v_a_1961_);
                            v___x_1964_ = l_Lean_MessageData_note(v___x_1963_);
                            v___x_1965_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1965_, 0, v___x_1957_);
                            leanh::lean_ctor_set(v___x_1965_, 1, v___x_1964_);
                            v_msg_1936_ = v___x_1965_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1957_, 2);
                            return v___x_1960_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1951_);
                        v_msg_1936_ = v___x_1957_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1942_);
                    v_a_1966_ = leanh::lean_ctor_get(v___x_1950_, 0);
                    v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v___x_1950_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1950_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1966_);
                        leanh::lean_dec(v___x_1950_);
                        v___x_1968_ = leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1937_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once),
                    _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2,
                );
                v___x_1938_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1938_, 0, v_msg_1936_);
                leanh::lean_ctor_set(v___x_1938_, 1, v___x_1937_);
                v___x_1939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                return v___x_1939_;
            }
            2 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(
    mut v_thm_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
    mut v_a_1976_: *mut leanh::LeanObject,
    mut v_a_1977_: *mut leanh::LeanObject,
    mut v_a_1978_: *mut leanh::LeanObject,
    mut v_a_1979_: *mut leanh::LeanObject,
    mut v_a_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
        v_thm_1974_,
        v_a_1975_,
        v_a_1976_,
        v_a_1977_,
        v_a_1978_,
        v_a_1979_,
        v_a_1980_,
        v_a_1981_,
    );
    leanh::lean_dec(v_a_1981_);
    leanh::lean_dec_ref(v_a_1980_);
    leanh::lean_dec(v_a_1979_);
    leanh::lean_dec_ref(v_a_1978_);
    leanh::lean_dec(v_a_1977_);
    leanh::lean_dec_ref(v_a_1976_);
    leanh::lean_dec(v_a_1975_);
    return v_res_1983_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(
    mut v___x_1984_: *mut leanh::LeanObject,
    mut v_as_1985_: *mut leanh::LeanObject,
    mut v_sz_1986_: usize,
    mut v_i_1987_: usize,
    mut v_b_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_1984_, v_as_1985_, v_sz_1986_, v_i_1987_, v_b_1988_);
    return v___x_1997_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(
    mut v___x_1998_: *mut leanh::LeanObject,
    mut v_as_1999_: *mut leanh::LeanObject,
    mut v_sz_2000_: *mut leanh::LeanObject,
    mut v_i_2001_: *mut leanh::LeanObject,
    mut v_b_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
    mut v___y_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2011_: usize = 0;
    let mut v_i_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2011_ = leanh::lean_unbox_usize(v_sz_2000_);
    leanh::lean_dec(v_sz_2000_);
    v_i_boxed_2012_ = leanh::lean_unbox_usize(v_i_2001_);
    leanh::lean_dec(v_i_2001_);
    v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_1998_, v_as_1999_, v_sz_boxed_2011_, v_i_boxed_2012_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
    leanh::lean_dec(v___y_2009_);
    leanh::lean_dec_ref(v___y_2008_);
    leanh::lean_dec(v___y_2007_);
    leanh::lean_dec_ref(v___y_2006_);
    leanh::lean_dec(v___y_2005_);
    leanh::lean_dec_ref(v___y_2004_);
    leanh::lean_dec(v___y_2003_);
    leanh::lean_dec_ref(v_as_1999_);
    leanh::lean_dec_ref(v___x_1998_);
    return v_res_2013_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(
    mut v_o_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = lean_st_ref_get(v___y_2015_);
    v_env_2018_ = leanh::lean_ctor_get(v___x_2017_, 0);
    leanh::lean_inc_ref(v_env_2018_);
    leanh::lean_dec(v___x_2017_);
    v___x_2019_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2020_ = leanh::lean_ctor_get(v___x_2019_, 0);
    v_asyncMode_2021_ = leanh::lean_ctor_get(v_toEnvExtension_2020_, 2);
    v___x_2022_ = leanh::lean_box(1);
    v___x_2023_ = leanh::lean_box(0);
    v_linterSets_2024_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2022_,
        v___x_2019_,
        v_env_2018_,
        v_asyncMode_2021_,
        v___x_2023_,
    );
    v___x_2025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2025_, 0, v_o_2014_);
    leanh::lean_ctor_set(v___x_2025_, 1, v_linterSets_2024_);
    v___x_2026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(
    mut v_o_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_2027_, v___y_2028_);
    leanh::lean_dec(v___y_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_2034_ = leanh::lean_ctor_get(v___y_2031_, 2);
    leanh::lean_inc_ref(v_options_2034_);
    v___x_2035_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_options_2034_, v___y_2032_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(
    mut v___y_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(
        v___y_2036_,
        v___y_2037_,
    );
    leanh::lean_dec(v___y_2037_);
    leanh::lean_dec_ref(v___y_2036_);
    return v_res_2039_;
}
pub unsafe fn l_Lean_Meta_Simp_shouldCheckLoops(
    mut v_force_2040_: u8,
    mut v_ctxt_2041_: *mut leanh::LeanObject,
    mut v_a_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_singlePass_2046_: u8 = 0;
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_2045_ = leanh::lean_ctor_get(v_ctxt_2041_, 0);
                v_singlePass_2046_ = leanh::lean_ctor_get_uint8(
                    v_config_2045_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                if v_singlePass_2046_ == 0 {
                    if v_force_2040_ == 0 {
                        v___x_2047_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_2042_, v_a_2043_);
                        v_a_2048_ = leanh::lean_ctor_get(v___x_2047_, 0);
                        v_isSharedCheck_2058_ =
                            (!leanh::lean_is_exclusive(v___x_2047_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v___x_2050_ = v___x_2047_;
                            v_isShared_2051_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2048_);
                            leanh::lean_dec(v___x_2047_);
                            v___x_2050_ = leanh::lean_box(0);
                            v_isShared_2051_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2059_ = leanh::lean_box((v_force_2040_) as usize);
                        v___x_2060_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
                        return v___x_2060_;
                    }
                } else {
                    v___x_2061_ = 0;
                    v___x_2062_ = leanh::lean_box((v___x_2061_) as usize);
                    v___x_2063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2063_, 0, v___x_2062_);
                    return v___x_2063_;
                }
            }
            1 => {
                v___x_2052_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
                v___x_2053_ = l_Lean_Linter_getLinterValue(v___x_2052_, v_a_2048_);
                leanh::lean_dec(v_a_2048_);
                v___x_2054_ = leanh::lean_box((v___x_2053_) as usize);
                if v_isShared_2051_ == 0 {
                    leanh::lean_ctor_set(v___x_2050_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_shouldCheckLoops___boxed(
    mut v_force_2064_: *mut leanh::LeanObject,
    mut v_ctxt_2065_: *mut leanh::LeanObject,
    mut v_a_2066_: *mut leanh::LeanObject,
    mut v_a_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_force_boxed_2069_: u8 = 0;
    let mut v_res_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_force_boxed_2069_ = (leanh::lean_unbox(v_force_2064_) as u8);
    v_res_2070_ =
        l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_2069_, v_ctxt_2065_, v_a_2066_, v_a_2067_);
    leanh::lean_dec(v_a_2067_);
    leanh::lean_dec_ref(v_a_2066_);
    leanh::lean_dec_ref(v_ctxt_2065_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(
    mut v_o_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
    mut v___y_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_2071_, v___y_2073_);
    return v___x_2075_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(
    mut v_o_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_2076_, v___y_2077_, v___y_2078_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2080_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(
    mut v_k_2081_: *mut leanh::LeanObject,
    mut v_b_2082_: *mut leanh::LeanObject,
    mut v_c_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2087_);
    leanh::lean_inc_ref(v___y_2086_);
    leanh::lean_inc(v___y_2085_);
    leanh::lean_inc_ref(v___y_2084_);
    v___x_2089_ = leanh::lean_apply_7(
        v_k_2081_,
        v_b_2082_,
        v_c_2083_,
        v___y_2084_,
        v___y_2085_,
        v___y_2086_,
        v___y_2087_,
        leanh::lean_box(0),
    );
    return v___x_2089_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(
    mut v_k_2090_: *mut leanh::LeanObject,
    mut v_b_2091_: *mut leanh::LeanObject,
    mut v_c_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_2090_, v_b_2091_, v_c_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
    leanh::lean_dec(v___y_2096_);
    leanh::lean_dec_ref(v___y_2095_);
    leanh::lean_dec(v___y_2094_);
    leanh::lean_dec_ref(v___y_2093_);
    return v_res_2098_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
    mut v_type_2099_: *mut leanh::LeanObject,
    mut v_k_2100_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2101_: u8,
    mut v_whnfType_2102_: u8,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut v_a_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2108_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2108_, 0, v_k_2100_);
                v___x_2109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_2099_,
                    v___f_2108_,
                    v_cleanupAnnotations_2101_,
                    v_whnfType_2102_,
                    v___y_2103_,
                    v___y_2104_,
                    v___y_2105_,
                    v___y_2106_,
                );
                if leanh::lean_obj_tag(v___x_2109_) == 0 {
                    v_a_2110_ = leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2117_ = (!leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2117_ == 0 {
                        v___x_2112_ = v___x_2109_;
                        v_isShared_2113_ = v_isSharedCheck_2117_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2110_);
                        leanh::lean_dec(v___x_2109_);
                        v___x_2112_ = leanh::lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2117_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2118_ = leanh::lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2125_ = (!leanh::lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2120_ = v___x_2109_;
                        v_isShared_2121_ = v_isSharedCheck_2125_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2118_);
                        leanh::lean_dec(v___x_2109_);
                        v___x_2120_ = leanh::lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2125_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2113_ == 0 {
                    v___x_2115_ = v___x_2112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2115_;
            }
            3 => {
                if v_isShared_2121_ == 0 {
                    v___x_2123_ = v___x_2120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
                    v___x_2123_ = v_reuseFailAlloc_2124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(
    mut v_type_2126_: *mut leanh::LeanObject,
    mut v_k_2127_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2128_: *mut leanh::LeanObject,
    mut v_whnfType_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2135_: u8 = 0;
    let mut v_whnfType_boxed_2136_: u8 = 0;
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2135_ = (leanh::lean_unbox(v_cleanupAnnotations_2128_) as u8);
    v_whnfType_boxed_2136_ = (leanh::lean_unbox(v_whnfType_2129_) as u8);
    v_res_2137_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
            v_type_2126_,
            v_k_2127_,
            v_cleanupAnnotations_boxed_2135_,
            v_whnfType_boxed_2136_,
            v___y_2130_,
            v___y_2131_,
            v___y_2132_,
            v___y_2133_,
        );
    leanh::lean_dec(v___y_2133_);
    leanh::lean_dec_ref(v___y_2132_);
    leanh::lean_dec(v___y_2131_);
    leanh::lean_dec_ref(v___y_2130_);
    return v_res_2137_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(
    mut v_00_u03b1_2138_: *mut leanh::LeanObject,
    mut v_type_2139_: *mut leanh::LeanObject,
    mut v_k_2140_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2141_: u8,
    mut v_whnfType_2142_: u8,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
            v_type_2139_,
            v_k_2140_,
            v_cleanupAnnotations_2141_,
            v_whnfType_2142_,
            v___y_2143_,
            v___y_2144_,
            v___y_2145_,
            v___y_2146_,
        );
    return v___x_2148_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(
    mut v_00_u03b1_2149_: *mut leanh::LeanObject,
    mut v_type_2150_: *mut leanh::LeanObject,
    mut v_k_2151_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2152_: *mut leanh::LeanObject,
    mut v_whnfType_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
    mut v___y_2156_: *mut leanh::LeanObject,
    mut v___y_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2159_: u8 = 0;
    let mut v_whnfType_boxed_2160_: u8 = 0;
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2159_ = (leanh::lean_unbox(v_cleanupAnnotations_2152_) as u8);
    v_whnfType_boxed_2160_ = (leanh::lean_unbox(v_whnfType_2153_) as u8);
    v_res_2161_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(
        v_00_u03b1_2149_,
        v_type_2150_,
        v_k_2151_,
        v_cleanupAnnotations_boxed_2159_,
        v_whnfType_boxed_2160_,
        v___y_2154_,
        v___y_2155_,
        v___y_2156_,
        v___y_2157_,
    );
    leanh::lean_dec(v___y_2157_);
    leanh::lean_dec_ref(v___y_2156_);
    leanh::lean_dec(v___y_2155_);
    leanh::lean_dec_ref(v___y_2154_);
    return v_res_2161_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(
    mut v_msgData_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_st_ref_get(v___y_2166_);
    v_env_2169_ = leanh::lean_ctor_get(v___x_2168_, 0);
    leanh::lean_inc_ref(v_env_2169_);
    leanh::lean_dec(v___x_2168_);
    v___x_2170_ = lean_st_ref_get(v___y_2164_);
    v_mctx_2171_ = leanh::lean_ctor_get(v___x_2170_, 0);
    leanh::lean_inc_ref(v_mctx_2171_);
    leanh::lean_dec(v___x_2170_);
    v_lctx_2172_ = leanh::lean_ctor_get(v___y_2163_, 2);
    v_options_2173_ = leanh::lean_ctor_get(v___y_2165_, 2);
    leanh::lean_inc_ref(v_options_2173_);
    leanh::lean_inc_ref(v_lctx_2172_);
    v___x_2174_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2174_, 0, v_env_2169_);
    leanh::lean_ctor_set(v___x_2174_, 1, v_mctx_2171_);
    leanh::lean_ctor_set(v___x_2174_, 2, v_lctx_2172_);
    leanh::lean_ctor_set(v___x_2174_, 3, v_options_2173_);
    v___x_2175_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
    leanh::lean_ctor_set(v___x_2175_, 1, v_msgData_2162_);
    v___x_2176_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    return v___x_2176_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(
    mut v_msgData_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
    mut v___y_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2183_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
    leanh::lean_dec(v___y_2181_);
    leanh::lean_dec_ref(v___y_2180_);
    leanh::lean_dec(v___y_2179_);
    leanh::lean_dec_ref(v___y_2178_);
    return v_res_2183_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: f64 = 0.0;
    v___x_2184_ = leanh::lean_unsigned_to_nat(0);
    v___x_2185_ = lean_float_of_nat(v___x_2184_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
    mut v_cls_2188_: *mut leanh::LeanObject,
    mut v_msg_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v___y_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v_tid_2214_: u64 = 0;
    let mut v_traces_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: f64 = 0.0;
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2195_ = leanh::lean_ctor_get(v___y_2192_, 5);
                v___x_2196_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
                v_a_2197_ = leanh::lean_ctor_get(v___x_2196_, 0);
                v_isSharedCheck_2241_ = (!leanh::lean_is_exclusive(v___x_2196_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v___x_2199_ = v___x_2196_;
                    v_isShared_2200_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2197_);
                    leanh::lean_dec(v___x_2196_);
                    v___x_2199_ = leanh::lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = lean_st_ref_take(v___y_2193_);
                v_traceState_2202_ = leanh::lean_ctor_get(v___x_2201_, 4);
                v_env_2203_ = leanh::lean_ctor_get(v___x_2201_, 0);
                v_nextMacroScope_2204_ = leanh::lean_ctor_get(v___x_2201_, 1);
                v_ngen_2205_ = leanh::lean_ctor_get(v___x_2201_, 2);
                v_auxDeclNGen_2206_ = leanh::lean_ctor_get(v___x_2201_, 3);
                v_cache_2207_ = leanh::lean_ctor_get(v___x_2201_, 5);
                v_messages_2208_ = leanh::lean_ctor_get(v___x_2201_, 6);
                v_infoState_2209_ = leanh::lean_ctor_get(v___x_2201_, 7);
                v_snapshotTasks_2210_ = leanh::lean_ctor_get(v___x_2201_, 8);
                v_isSharedCheck_2240_ = (!leanh::lean_is_exclusive(v___x_2201_)) as u8;
                if v_isSharedCheck_2240_ == 0 {
                    v___x_2212_ = v___x_2201_;
                    v_isShared_2213_ = v_isSharedCheck_2240_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2210_);
                    leanh::lean_inc(v_infoState_2209_);
                    leanh::lean_inc(v_messages_2208_);
                    leanh::lean_inc(v_cache_2207_);
                    leanh::lean_inc(v_traceState_2202_);
                    leanh::lean_inc(v_auxDeclNGen_2206_);
                    leanh::lean_inc(v_ngen_2205_);
                    leanh::lean_inc(v_nextMacroScope_2204_);
                    leanh::lean_inc(v_env_2203_);
                    leanh::lean_dec(v___x_2201_);
                    v___x_2212_ = leanh::lean_box(0);
                    v_isShared_2213_ = v_isSharedCheck_2240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2214_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2202_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2215_ = leanh::lean_ctor_get(v_traceState_2202_, 0);
                v_isSharedCheck_2239_ =
                    (!leanh::lean_is_exclusive(v_traceState_2202_)) as u8;
                if v_isSharedCheck_2239_ == 0 {
                    v___x_2217_ = v_traceState_2202_;
                    v_isShared_2218_ = v_isSharedCheck_2239_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2215_);
                    leanh::lean_dec(v_traceState_2202_);
                    v___x_2217_ = leanh::lean_box(0);
                    v_isShared_2218_ = v_isSharedCheck_2239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2219_ = leanh::lean_box(0);
                v___x_2220_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
                v___x_2221_ = 0;
                v___x_2222_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
                v___x_2223_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_2223_, 0, v_cls_2188_);
                leanh::lean_ctor_set(v___x_2223_, 1, v___x_2219_);
                leanh::lean_ctor_set(v___x_2223_, 2, v___x_2222_);
                leanh::lean_ctor_set_float(
                    v___x_2223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2220_,
                );
                leanh::lean_ctor_set_float(
                    v___x_2223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2220_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2221_,
                );
                v___x_2224_ =
                    l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1;
                v___x_2225_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2225_, 0, v___x_2223_);
                leanh::lean_ctor_set(v___x_2225_, 1, v_a_2197_);
                leanh::lean_ctor_set(v___x_2225_, 2, v___x_2224_);
                leanh::lean_inc(v_ref_2195_);
                v___x_2226_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2226_, 0, v_ref_2195_);
                leanh::lean_ctor_set(v___x_2226_, 1, v___x_2225_);
                v___x_2227_ = l_Lean_PersistentArray_push___redArg(v_traces_2215_, v___x_2226_);
                if v_isShared_2218_ == 0 {
                    leanh::lean_ctor_set(v___x_2217_, 0, v___x_2227_);
                    v___x_2229_ = v___x_2217_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2227_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2214_,
                    );
                    v___x_2229_ = v_reuseFailAlloc_2238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2213_ == 0 {
                    leanh::lean_ctor_set(v___x_2212_, 4, v___x_2229_);
                    v___x_2231_ = v___x_2212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_env_2203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_nextMacroScope_2204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_ngen_2205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_auxDeclNGen_2206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 4, v___x_2229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 5, v_cache_2207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 6, v_messages_2208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 7, v_infoState_2209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 8, v_snapshotTasks_2210_);
                    v___x_2231_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2232_ = lean_st_ref_set(v___y_2193_, v___x_2231_);
                v___x_2233_ = leanh::lean_box(0);
                if v_isShared_2200_ == 0 {
                    leanh::lean_ctor_set(v___x_2199_, 0, v___x_2233_);
                    v___x_2235_ = v___x_2199_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(
    mut v_cls_2242_: *mut leanh::LeanObject,
    mut v_msg_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2249_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
        v_cls_2242_,
        v_msg_2243_,
        v___y_2244_,
        v___y_2245_,
        v___y_2246_,
        v___y_2247_,
    );
    leanh::lean_dec(v___y_2247_);
    leanh::lean_dec_ref(v___y_2246_);
    leanh::lean_dec(v___y_2245_);
    leanh::lean_dec_ref(v___y_2244_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(
    mut v_opts_2250_: *mut leanh::LeanObject,
    mut v_opt_2251_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2252_ = leanh::lean_ctor_get(v_opt_2251_, 0);
    v_defValue_2253_ = leanh::lean_ctor_get(v_opt_2251_, 1);
    v_map_2254_ = leanh::lean_ctor_get(v_opts_2250_, 0);
    v___x_2255_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2254_,
            v_name_2252_,
        );
    if leanh::lean_obj_tag(v___x_2255_) == 0 {
        let mut v___x_2256_: u8 = 0;
        v___x_2256_ = (leanh::lean_unbox(v_defValue_2253_) as u8);
        return v___x_2256_;
    } else {
        let mut v_val_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2257_ = leanh::lean_ctor_get(v___x_2255_, 0);
        leanh::lean_inc(v_val_2257_);
        leanh::lean_dec_ref_known(v___x_2255_, 1);
        if leanh::lean_obj_tag(v_val_2257_) == 1 {
            let mut v_v_2258_: u8 = 0;
            v_v_2258_ = leanh::lean_ctor_get_uint8(v_val_2257_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2257_, 0);
            return v_v_2258_;
        } else {
            let mut v___x_2259_: u8 = 0;
            leanh::lean_dec(v_val_2257_);
            v___x_2259_ = (leanh::lean_unbox(v_defValue_2253_) as u8);
            return v___x_2259_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_opts_2260_: *mut leanh::LeanObject,
    mut v_opt_2261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2262_: u8 = 0;
    let mut v_r_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_2260_, v_opt_2261_);
    leanh::lean_dec_ref(v_opt_2261_);
    leanh::lean_dec_ref(v_opts_2260_);
    v_r_2263_ = leanh::lean_box((v_res_2262_) as usize);
    return v_r_2263_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v___y_2272_: u8,
    mut v_suppressElabErrors_2273_: u8,
    mut v_x_2274_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2274_) == 1 {
        let mut v_pre_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2275_ = leanh::lean_ctor_get(v_x_2274_, 0);
        match leanh::lean_obj_tag(v_pre_2275_) {
            1 => {
                let mut v_pre_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2276_ = leanh::lean_ctor_get(v_pre_2275_, 0);
                match leanh::lean_obj_tag(v_pre_2276_) {
                    0 => {
                        let mut v_str_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2280_: u8 = 0;
                        v_str_2277_ = leanh::lean_ctor_get(v_x_2274_, 1);
                        v_str_2278_ = leanh::lean_ctor_get(v_pre_2275_, 1);
                        v___x_2279_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0;
                        v___x_2280_ = lean_string_dec_eq(v_str_2278_, v___x_2279_);
                        if v___x_2280_ == 0 {
                            let mut v___x_2281_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2282_: u8 = 0;
                            v___x_2281_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
                            v___x_2282_ = lean_string_dec_eq(v_str_2278_, v___x_2281_);
                            if v___x_2282_ == 0 {
                                return v___y_2272_;
                            } else {
                                let mut v___x_2283_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2284_: u8 = 0;
                                v___x_2283_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2;
                                v___x_2284_ = lean_string_dec_eq(v_str_2277_, v___x_2283_);
                                if v___x_2284_ == 0 {
                                    return v___y_2272_;
                                } else {
                                    return v_suppressElabErrors_2273_;
                                }
                            }
                        } else {
                            let mut v___x_2285_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2286_: u8 = 0;
                            v___x_2285_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3;
                            v___x_2286_ = lean_string_dec_eq(v_str_2277_, v___x_2285_);
                            if v___x_2286_ == 0 {
                                return v___y_2272_;
                            } else {
                                return v_suppressElabErrors_2273_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2287_ = leanh::lean_ctor_get(v_pre_2276_, 0);
                        if leanh::lean_obj_tag(v_pre_2287_) == 0 {
                            let mut v_str_2288_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2289_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2290_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2291_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2292_: u8 = 0;
                            v_str_2288_ = leanh::lean_ctor_get(v_x_2274_, 1);
                            v_str_2289_ = leanh::lean_ctor_get(v_pre_2275_, 1);
                            v_str_2290_ = leanh::lean_ctor_get(v_pre_2276_, 1);
                            v___x_2291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4;
                            v___x_2292_ = lean_string_dec_eq(v_str_2290_, v___x_2291_);
                            if v___x_2292_ == 0 {
                                return v___y_2272_;
                            } else {
                                let mut v___x_2293_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2294_: u8 = 0;
                                v___x_2293_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5;
                                v___x_2294_ = lean_string_dec_eq(v_str_2289_, v___x_2293_);
                                if v___x_2294_ == 0 {
                                    return v___y_2272_;
                                } else {
                                    let mut v___x_2295_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2296_: u8 = 0;
                                    v___x_2295_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6;
                                    v___x_2296_ = lean_string_dec_eq(v_str_2288_, v___x_2295_);
                                    if v___x_2296_ == 0 {
                                        return v___y_2272_;
                                    } else {
                                        return v_suppressElabErrors_2273_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2272_;
                        }
                    }
                    _ => {
                        return v___y_2272_;
                    }
                }
            }
            0 => {
                let mut v_str_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2299_: u8 = 0;
                v_str_2297_ = leanh::lean_ctor_get(v_x_2274_, 1);
                v___x_2298_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7;
                v___x_2299_ = lean_string_dec_eq(v_str_2297_, v___x_2298_);
                if v___x_2299_ == 0 {
                    return v___y_2272_;
                } else {
                    return v_suppressElabErrors_2273_;
                }
            }
            _ => {
                return v___y_2272_;
            }
        }
    } else {
        return v___y_2272_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2301_: *mut leanh::LeanObject,
    mut v_x_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_24906__boxed_2303_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2304_: u8 = 0;
    let mut v_res_2305_: u8 = 0;
    let mut v_r_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_24906__boxed_2303_ = (leanh::lean_unbox(v___y_2300_) as u8);
    v_suppressElabErrors_boxed_2304_ = (leanh::lean_unbox(v_suppressElabErrors_2301_) as u8);
    v_res_2305_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v___y_24906__boxed_2303_, v_suppressElabErrors_boxed_2304_, v_x_2302_);
    leanh::lean_dec(v_x_2302_);
    v_r_2306_ = leanh::lean_box((v_res_2305_) as usize);
    return v_r_2306_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(
    mut v_ref_2307_: *mut leanh::LeanObject,
    mut v_msgData_2308_: *mut leanh::LeanObject,
    mut v_severity_2309_: u8,
    mut v_isSilent_2310_: u8,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2318_: u8 = 0;
    let mut v___y_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: u8 = 0;
    let mut v___y_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v___y_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2354_: u8 = 0;
    let mut v___y_2355_: u8 = 0;
    let mut v___y_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: u8 = 0;
    let mut v___y_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v___y_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: u8 = 0;
    let mut v___y_2381_: u8 = 0;
    let mut v___y_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: u8 = 0;
    let mut v___y_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: u8 = 0;
    let mut v___y_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2394_: u8 = 0;
    let mut v___y_2395_: u8 = 0;
    let mut v_ref_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___y_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: u8 = 0;
    let mut v___y_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: u8 = 0;
    let mut v___y_2408_: u8 = 0;
    let mut v___y_2410_: u8 = 0;
    let mut v_fileName_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2400_ = 2;
                v___x_2425_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2400_);
                if v___x_2425_ == 0 {
                    v___y_2410_ = v___x_2425_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2308_);
                    v___x_2426_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2308_);
                    v___y_2410_ = v___x_2426_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2326_ = lean_st_ref_take(v___y_2325_);
                v_currNamespace_2327_ = leanh::lean_ctor_get(v___y_2324_, 6);
                v_openDecls_2328_ = leanh::lean_ctor_get(v___y_2324_, 7);
                v_env_2329_ = leanh::lean_ctor_get(v___x_2326_, 0);
                v_nextMacroScope_2330_ = leanh::lean_ctor_get(v___x_2326_, 1);
                v_ngen_2331_ = leanh::lean_ctor_get(v___x_2326_, 2);
                v_auxDeclNGen_2332_ = leanh::lean_ctor_get(v___x_2326_, 3);
                v_traceState_2333_ = leanh::lean_ctor_get(v___x_2326_, 4);
                v_cache_2334_ = leanh::lean_ctor_get(v___x_2326_, 5);
                v_messages_2335_ = leanh::lean_ctor_get(v___x_2326_, 6);
                v_infoState_2336_ = leanh::lean_ctor_get(v___x_2326_, 7);
                v_snapshotTasks_2337_ = leanh::lean_ctor_get(v___x_2326_, 8);
                v_isSharedCheck_2351_ = (!leanh::lean_is_exclusive(v___x_2326_)) as u8;
                if v_isSharedCheck_2351_ == 0 {
                    v___x_2339_ = v___x_2326_;
                    v_isShared_2340_ = v_isSharedCheck_2351_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2337_);
                    leanh::lean_inc(v_infoState_2336_);
                    leanh::lean_inc(v_messages_2335_);
                    leanh::lean_inc(v_cache_2334_);
                    leanh::lean_inc(v_traceState_2333_);
                    leanh::lean_inc(v_auxDeclNGen_2332_);
                    leanh::lean_inc(v_ngen_2331_);
                    leanh::lean_inc(v_nextMacroScope_2330_);
                    leanh::lean_inc(v_env_2329_);
                    leanh::lean_dec(v___x_2326_);
                    v___x_2339_ = leanh::lean_box(0);
                    v_isShared_2340_ = v_isSharedCheck_2351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2328_);
                leanh::lean_inc(v_currNamespace_2327_);
                v___x_2341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2341_, 0, v_currNamespace_2327_);
                leanh::lean_ctor_set(v___x_2341_, 1, v_openDecls_2328_);
                v___x_2342_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                leanh::lean_ctor_set(v___x_2342_, 1, v___y_2320_);
                leanh::lean_inc_ref(v___y_2317_);
                leanh::lean_inc_ref(v___y_2323_);
                v___x_2343_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2343_, 0, v___y_2323_);
                leanh::lean_ctor_set(v___x_2343_, 1, v___y_2319_);
                leanh::lean_ctor_set(v___x_2343_, 2, v___y_2321_);
                leanh::lean_ctor_set(v___x_2343_, 3, v___y_2317_);
                leanh::lean_ctor_set(v___x_2343_, 4, v___x_2342_);
                leanh::lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2322_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2318_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2310_,
                );
                v___x_2344_ = l_Lean_MessageLog_add(v___x_2343_, v_messages_2335_);
                if v_isShared_2340_ == 0 {
                    leanh::lean_ctor_set(v___x_2339_, 6, v___x_2344_);
                    v___x_2346_ = v___x_2339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_env_2329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_nextMacroScope_2330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_ngen_2331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_auxDeclNGen_2332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_traceState_2333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_cache_2334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 6, v___x_2344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 7, v_infoState_2336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 8, v_snapshotTasks_2337_);
                    v___x_2346_ = v_reuseFailAlloc_2350_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2347_ = lean_st_ref_set(v___y_2325_, v___x_2346_);
                v___x_2348_ = leanh::lean_box(0);
                v___x_2349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2349_, 0, v___x_2348_);
                return v___x_2349_;
            }
            4 => {
                v___x_2361_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2308_,
                    );
                v___x_2362_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_2361_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
                v_a_2363_ = leanh::lean_ctor_get(v___x_2362_, 0);
                v_isSharedCheck_2376_ = (!leanh::lean_is_exclusive(v___x_2362_)) as u8;
                if v_isSharedCheck_2376_ == 0 {
                    v___x_2365_ = v___x_2362_;
                    v_isShared_2366_ = v_isSharedCheck_2376_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2363_);
                    leanh::lean_dec(v___x_2362_);
                    v___x_2365_ = leanh::lean_box(0);
                    v_isShared_2366_ = v_isSharedCheck_2376_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2357_, 2);
                v___x_2367_ = l_Lean_FileMap_toPosition(v___y_2357_, v___y_2356_);
                leanh::lean_dec(v___y_2356_);
                v___x_2368_ = l_Lean_FileMap_toPosition(v___y_2357_, v___y_2360_);
                leanh::lean_dec(v___y_2360_);
                v___x_2369_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                v___x_2370_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
                if v___y_2355_ == 0 {
                    leanh::lean_del_object(v___x_2365_);
                    leanh::lean_dec_ref(v___y_2353_);
                    v___y_2317_ = v___x_2370_;
                    v___y_2318_ = v___y_2354_;
                    v___y_2319_ = v___x_2367_;
                    v___y_2320_ = v_a_2363_;
                    v___y_2321_ = v___x_2369_;
                    v___y_2322_ = v___y_2359_;
                    v___y_2323_ = v___y_2358_;
                    v___y_2324_ = v___y_2313_;
                    v___y_2325_ = v___y_2314_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2363_);
                    v___x_2371_ = l_Lean_MessageData_hasTag(v___y_2353_, v_a_2363_);
                    if v___x_2371_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2369_, 1);
                        leanh::lean_dec_ref(v___x_2367_);
                        leanh::lean_dec(v_a_2363_);
                        v___x_2372_ = leanh::lean_box(0);
                        if v_isShared_2366_ == 0 {
                            leanh::lean_ctor_set(v___x_2365_, 0, v___x_2372_);
                            v___x_2374_ = v___x_2365_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2375_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
                            v___x_2374_ = v_reuseFailAlloc_2375_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2365_);
                        v___y_2317_ = v___x_2370_;
                        v___y_2318_ = v___y_2354_;
                        v___y_2319_ = v___x_2367_;
                        v___y_2320_ = v_a_2363_;
                        v___y_2321_ = v___x_2369_;
                        v___y_2322_ = v___y_2359_;
                        v___y_2323_ = v___y_2358_;
                        v___y_2324_ = v___y_2313_;
                        v___y_2325_ = v___y_2314_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2374_;
            }
            7 => {
                v___x_2386_ = l_Lean_Syntax_getTailPos_x3f(v___y_2379_, v___y_2383_);
                leanh::lean_dec(v___y_2379_);
                if leanh::lean_obj_tag(v___x_2386_) == 0 {
                    leanh::lean_inc(v___y_2385_);
                    v___y_2353_ = v___y_2378_;
                    v___y_2354_ = v___y_2380_;
                    v___y_2355_ = v___y_2381_;
                    v___y_2356_ = v___y_2385_;
                    v___y_2357_ = v___y_2382_;
                    v___y_2358_ = v___y_2384_;
                    v___y_2359_ = v___y_2383_;
                    v___y_2360_ = v___y_2385_;
                    state = 4;
                    continue;
                } else {
                    v_val_2387_ = leanh::lean_ctor_get(v___x_2386_, 0);
                    leanh::lean_inc(v_val_2387_);
                    leanh::lean_dec_ref_known(v___x_2386_, 1);
                    v___y_2353_ = v___y_2378_;
                    v___y_2354_ = v___y_2380_;
                    v___y_2355_ = v___y_2381_;
                    v___y_2356_ = v___y_2385_;
                    v___y_2357_ = v___y_2382_;
                    v___y_2358_ = v___y_2384_;
                    v___y_2359_ = v___y_2383_;
                    v___y_2360_ = v_val_2387_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2396_ = l_Lean_replaceRef(v_ref_2307_, v___y_2391_);
                v___x_2397_ = l_Lean_Syntax_getPos_x3f(v_ref_2396_, v___y_2394_);
                if leanh::lean_obj_tag(v___x_2397_) == 0 {
                    v___x_2398_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2378_ = v___y_2389_;
                    v___y_2379_ = v_ref_2396_;
                    v___y_2380_ = v___y_2395_;
                    v___y_2381_ = v___y_2390_;
                    v___y_2382_ = v___y_2392_;
                    v___y_2383_ = v___y_2394_;
                    v___y_2384_ = v___y_2393_;
                    v___y_2385_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_val_2399_ = leanh::lean_ctor_get(v___x_2397_, 0);
                    leanh::lean_inc(v_val_2399_);
                    leanh::lean_dec_ref_known(v___x_2397_, 1);
                    v___y_2378_ = v___y_2389_;
                    v___y_2379_ = v_ref_2396_;
                    v___y_2380_ = v___y_2395_;
                    v___y_2381_ = v___y_2390_;
                    v___y_2382_ = v___y_2392_;
                    v___y_2383_ = v___y_2394_;
                    v___y_2384_ = v___y_2393_;
                    v___y_2385_ = v_val_2399_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2408_ == 0 {
                    v___y_2389_ = v___y_2405_;
                    v___y_2390_ = v___y_2403_;
                    v___y_2391_ = v___y_2402_;
                    v___y_2392_ = v___y_2404_;
                    v___y_2393_ = v___y_2406_;
                    v___y_2394_ = v___y_2407_;
                    v___y_2395_ = v_severity_2309_;
                    state = 8;
                    continue;
                } else {
                    v___y_2389_ = v___y_2405_;
                    v___y_2390_ = v___y_2403_;
                    v___y_2391_ = v___y_2402_;
                    v___y_2392_ = v___y_2404_;
                    v___y_2393_ = v___y_2406_;
                    v___y_2394_ = v___y_2407_;
                    v___y_2395_ = v___x_2400_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2410_ == 0 {
                    v_fileName_2411_ = leanh::lean_ctor_get(v___y_2313_, 0);
                    v_fileMap_2412_ = leanh::lean_ctor_get(v___y_2313_, 1);
                    v_options_2413_ = leanh::lean_ctor_get(v___y_2313_, 2);
                    v_ref_2414_ = leanh::lean_ctor_get(v___y_2313_, 5);
                    v_suppressElabErrors_2415_ = leanh::lean_ctor_get_uint8(
                        v___y_2313_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2416_ = leanh::lean_box((v___y_2410_) as usize);
                    v___x_2417_ = leanh::lean_box((v_suppressElabErrors_2415_) as usize);
                    v___f_2418_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2418_, 0, v___x_2416_);
                    leanh::lean_closure_set(v___f_2418_, 1, v___x_2417_);
                    v___x_2419_ = 1;
                    v___x_2420_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2419_);
                    if v___x_2420_ == 0 {
                        v___y_2402_ = v_ref_2414_;
                        v___y_2403_ = v_suppressElabErrors_2415_;
                        v___y_2404_ = v_fileMap_2412_;
                        v___y_2405_ = v___f_2418_;
                        v___y_2406_ = v_fileName_2411_;
                        v___y_2407_ = v___y_2410_;
                        v___y_2408_ = v___x_2420_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2421_ = l_Lean_warningAsError;
                        v___x_2422_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_options_2413_, v___x_2421_);
                        v___y_2402_ = v_ref_2414_;
                        v___y_2403_ = v_suppressElabErrors_2415_;
                        v___y_2404_ = v_fileMap_2412_;
                        v___y_2405_ = v___f_2418_;
                        v___y_2406_ = v_fileName_2411_;
                        v___y_2407_ = v___y_2410_;
                        v___y_2408_ = v___x_2422_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2308_);
                    v___x_2423_ = leanh::lean_box(0);
                    v___x_2424_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2424_, 0, v___x_2423_);
                    return v___x_2424_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_2427_: *mut leanh::LeanObject,
    mut v_msgData_2428_: *mut leanh::LeanObject,
    mut v_severity_2429_: *mut leanh::LeanObject,
    mut v_isSilent_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
    mut v___y_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2436_: u8 = 0;
    let mut v_isSilent_boxed_2437_: u8 = 0;
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2436_ = (leanh::lean_unbox(v_severity_2429_) as u8);
    v_isSilent_boxed_2437_ = (leanh::lean_unbox(v_isSilent_2430_) as u8);
    v_res_2438_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2427_, v_msgData_2428_, v_severity_boxed_2436_, v_isSilent_boxed_2437_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
    leanh::lean_dec(v___y_2434_);
    leanh::lean_dec_ref(v___y_2433_);
    leanh::lean_dec(v___y_2432_);
    leanh::lean_dec_ref(v___y_2431_);
    leanh::lean_dec(v_ref_2427_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(
    mut v_ref_2439_: *mut leanh::LeanObject,
    mut v_msgData_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
    mut v___y_2444_: *mut leanh::LeanObject,
    mut v___y_2445_: *mut leanh::LeanObject,
    mut v___y_2446_: *mut leanh::LeanObject,
    mut v___y_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = 1;
    v___x_2450_ = 0;
    v___x_2451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2439_, v_msgData_2440_, v___x_2449_, v___x_2450_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
    return v___x_2451_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(
    mut v_ref_2452_: *mut leanh::LeanObject,
    mut v_msgData_2453_: *mut leanh::LeanObject,
    mut v___y_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
    mut v___y_2456_: *mut leanh::LeanObject,
    mut v___y_2457_: *mut leanh::LeanObject,
    mut v___y_2458_: *mut leanh::LeanObject,
    mut v___y_2459_: *mut leanh::LeanObject,
    mut v___y_2460_: *mut leanh::LeanObject,
    mut v___y_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_2452_, v_msgData_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
    leanh::lean_dec(v___y_2460_);
    leanh::lean_dec_ref(v___y_2459_);
    leanh::lean_dec(v___y_2458_);
    leanh::lean_dec_ref(v___y_2457_);
    leanh::lean_dec(v___y_2456_);
    leanh::lean_dec_ref(v___y_2455_);
    leanh::lean_dec(v___y_2454_);
    leanh::lean_dec(v_ref_2452_);
    return v_res_2462_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0;
    v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
    return v___x_2465_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2467_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2;
    v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
    mut v_linterOption_2469_: *mut leanh::LeanObject,
    mut v_stx_2470_: *mut leanh::LeanObject,
    mut v_msg_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_unused_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2480_ = leanh::lean_ctor_get(v_linterOption_2469_, 0);
                v_isSharedCheck_2497_ =
                    (!leanh::lean_is_exclusive(v_linterOption_2469_)) as u8;
                if v_isSharedCheck_2497_ == 0 {
                    v_unused_2498_ = leanh::lean_ctor_get(v_linterOption_2469_, 1);
                    leanh::lean_dec(v_unused_2498_);
                    v___x_2482_ = v_linterOption_2469_;
                    v_isShared_2483_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_2480_);
                    leanh::lean_dec(v_linterOption_2469_);
                    v___x_2482_ = leanh::lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
                leanh::lean_inc(v_name_2480_);
                v___x_2485_ = l_Lean_MessageData_ofName(v_name_2480_);
                if v_isShared_2483_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2482_, 7);
                    leanh::lean_ctor_set(v___x_2482_, 1, v___x_2485_);
                    leanh::lean_ctor_set(v___x_2482_, 0, v___x_2484_);
                    v___x_2487_ = v___x_2482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2485_);
                    v___x_2487_ = v_reuseFailAlloc_2496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2488_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
                v___x_2489_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2489_, 0, v___x_2487_);
                leanh::lean_ctor_set(v___x_2489_, 1, v___x_2488_);
                v_disable_2490_ = l_Lean_MessageData_note(v___x_2489_);
                v___x_2491_ = l_Lean_Linter_linterMessageTag;
                v___x_2492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2492_, 0, v_msg_2471_);
                leanh::lean_ctor_set(v___x_2492_, 1, v_disable_2490_);
                v___x_2493_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2493_, 0, v___x_2491_);
                leanh::lean_ctor_set(v___x_2493_, 1, v___x_2492_);
                v___x_2494_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2494_, 0, v_name_2480_);
                leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                v___x_2495_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_2470_, v___x_2494_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(
    mut v_linterOption_2499_: *mut leanh::LeanObject,
    mut v_stx_2500_: *mut leanh::LeanObject,
    mut v_msg_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
    mut v___y_2506_: *mut leanh::LeanObject,
    mut v___y_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
    mut v___y_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
        v_linterOption_2499_,
        v_stx_2500_,
        v_msg_2501_,
        v___y_2502_,
        v___y_2503_,
        v___y_2504_,
        v___y_2505_,
        v___y_2506_,
        v___y_2507_,
        v___y_2508_,
    );
    leanh::lean_dec(v___y_2508_);
    leanh::lean_dec_ref(v___y_2507_);
    leanh::lean_dec(v___y_2506_);
    leanh::lean_dec_ref(v___y_2505_);
    leanh::lean_dec(v___y_2504_);
    leanh::lean_dec_ref(v___y_2503_);
    leanh::lean_dec(v___y_2502_);
    leanh::lean_dec(v_stx_2500_);
    return v_res_2510_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
    mut v_msgData_2511_: *mut leanh::LeanObject,
    mut v_severity_2512_: u8,
    mut v_isSilent_2513_: u8,
    mut v___y_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
    mut v___y_2518_: *mut leanh::LeanObject,
    mut v___y_2519_: *mut leanh::LeanObject,
    mut v___y_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2522_ = leanh::lean_ctor_get(v___y_2519_, 5);
    v___x_2523_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2522_, v_msgData_2511_, v_severity_2512_, v_isSilent_2513_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
    return v___x_2523_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(
    mut v_msgData_2524_: *mut leanh::LeanObject,
    mut v_severity_2525_: *mut leanh::LeanObject,
    mut v_isSilent_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2535_: u8 = 0;
    let mut v_isSilent_boxed_2536_: u8 = 0;
    let mut v_res_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2535_ = (leanh::lean_unbox(v_severity_2525_) as u8);
    v_isSilent_boxed_2536_ = (leanh::lean_unbox(v_isSilent_2526_) as u8);
    v_res_2537_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
            v_msgData_2524_,
            v_severity_boxed_2535_,
            v_isSilent_boxed_2536_,
            v___y_2527_,
            v___y_2528_,
            v___y_2529_,
            v___y_2530_,
            v___y_2531_,
            v___y_2532_,
            v___y_2533_,
        );
    leanh::lean_dec(v___y_2533_);
    leanh::lean_dec_ref(v___y_2532_);
    leanh::lean_dec(v___y_2531_);
    leanh::lean_dec_ref(v___y_2530_);
    leanh::lean_dec(v___y_2529_);
    leanh::lean_dec_ref(v___y_2528_);
    leanh::lean_dec(v___y_2527_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
    mut v_msgData_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
    mut v___y_2540_: *mut leanh::LeanObject,
    mut v___y_2541_: *mut leanh::LeanObject,
    mut v___y_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = 1;
    v___x_2548_ = 0;
    v___x_2549_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
            v_msgData_2538_,
            v___x_2547_,
            v___x_2548_,
            v___y_2539_,
            v___y_2540_,
            v___y_2541_,
            v___y_2542_,
            v___y_2543_,
            v___y_2544_,
            v___y_2545_,
        );
    return v___x_2549_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(
    mut v_msgData_2550_: *mut leanh::LeanObject,
    mut v___y_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
    mut v___y_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
        v_msgData_2550_,
        v___y_2551_,
        v___y_2552_,
        v___y_2553_,
        v___y_2554_,
        v___y_2555_,
        v___y_2556_,
        v___y_2557_,
    );
    leanh::lean_dec(v___y_2557_);
    leanh::lean_dec_ref(v___y_2556_);
    leanh::lean_dec(v___y_2555_);
    leanh::lean_dec_ref(v___y_2554_);
    leanh::lean_dec(v___y_2553_);
    leanh::lean_dec_ref(v___y_2552_);
    leanh::lean_dec(v___y_2551_);
    return v_res_2559_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2569_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__2;
    v___x_2570_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__3;
    v___x_2571_ = l_Lean_Name_append(v___x_2570_, v___x_2569_);
    return v___x_2571_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__5;
    v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__7;
    v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
    return v___x_2577_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__0(
    mut v___x_2578_: *mut leanh::LeanObject,
    mut v_force_2579_: u8,
    mut v_thm_2580_: *mut leanh::LeanObject,
    mut v_origin_2581_: *mut leanh::LeanObject,
    mut v___y_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
    mut v___y_2584_: *mut leanh::LeanObject,
    mut v___y_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
    mut v___y_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2636_: u8 = 0;
    let mut v_options_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2638_: u8 = 0;
    let mut v_inheritedTraceOptions_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2588_);
                leanh::lean_inc_ref(v___y_2587_);
                leanh::lean_inc(v___y_2586_);
                leanh::lean_inc_ref(v___y_2585_);
                leanh::lean_inc(v___y_2584_);
                leanh::lean_inc_ref(v___y_2583_);
                leanh::lean_inc(v___y_2582_);
                v___x_2622_ = lean_simp(
                    v___x_2578_,
                    v___y_2582_,
                    v___y_2583_,
                    v___y_2584_,
                    v___y_2585_,
                    v___y_2586_,
                    v___y_2587_,
                    v___y_2588_,
                );
                if leanh::lean_obj_tag(v___x_2622_) == 0 {
                    leanh::lean_dec(v___y_2582_);
                    leanh::lean_dec_ref(v_origin_2581_);
                    leanh::lean_dec_ref(v_thm_2580_);
                    v_isSharedCheck_2630_ = (!leanh::lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2630_ == 0 {
                        v_unused_2631_ = leanh::lean_ctor_get(v___x_2622_, 0);
                        leanh::lean_dec(v_unused_2631_);
                        v___x_2624_ = v___x_2622_;
                        v_isShared_2625_ = v_isSharedCheck_2630_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2622_);
                        v___x_2624_ = leanh::lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2630_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_2632_ = leanh::lean_ctor_get(v___x_2622_, 0);
                    v_isSharedCheck_2656_ = (!leanh::lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2634_ = v___x_2622_;
                        v_isShared_2635_ = v_isSharedCheck_2656_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2632_);
                        leanh::lean_dec(v___x_2622_);
                        v___x_2634_ = leanh::lean_box(0);
                        v_isShared_2635_ = v_isSharedCheck_2656_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if v_force_2579_ == 0 {
                    v___x_2598_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
                        v_thm_2580_,
                        v___y_2591_,
                        v___y_2592_,
                        v___y_2593_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if leanh::lean_obj_tag(v___x_2598_) == 0 {
                        v_a_2599_ = leanh::lean_ctor_get(v___x_2598_, 0);
                        leanh::lean_inc(v_a_2599_);
                        leanh::lean_dec_ref_known(v___x_2598_, 1);
                        v_ref_2600_ = leanh::lean_ctor_get(v___y_2596_, 5);
                        v___x_2601_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
                        v___x_2602_ =
                            l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
                                v___x_2601_,
                                v_ref_2600_,
                                v_a_2599_,
                                v___y_2591_,
                                v___y_2592_,
                                v___y_2593_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                        leanh::lean_dec(v___y_2591_);
                        return v___x_2602_;
                    } else {
                        leanh::lean_dec(v___y_2591_);
                        v_a_2603_ = leanh::lean_ctor_get(v___x_2598_, 0);
                        v_isSharedCheck_2610_ =
                            (!leanh::lean_is_exclusive(v___x_2598_)) as u8;
                        if v_isSharedCheck_2610_ == 0 {
                            v___x_2605_ = v___x_2598_;
                            v_isShared_2606_ = v_isSharedCheck_2610_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2603_);
                            leanh::lean_dec(v___x_2598_);
                            v___x_2605_ = leanh::lean_box(0);
                            v_isShared_2606_ = v_isSharedCheck_2610_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2611_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
                        v_thm_2580_,
                        v___y_2591_,
                        v___y_2592_,
                        v___y_2593_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if leanh::lean_obj_tag(v___x_2611_) == 0 {
                        v_a_2612_ = leanh::lean_ctor_get(v___x_2611_, 0);
                        leanh::lean_inc(v_a_2612_);
                        leanh::lean_dec_ref_known(v___x_2611_, 1);
                        v___x_2613_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
                            v_a_2612_,
                            v___y_2591_,
                            v___y_2592_,
                            v___y_2593_,
                            v___y_2594_,
                            v___y_2595_,
                            v___y_2596_,
                            v___y_2597_,
                        );
                        leanh::lean_dec(v___y_2591_);
                        return v___x_2613_;
                    } else {
                        leanh::lean_dec(v___y_2591_);
                        v_a_2614_ = leanh::lean_ctor_get(v___x_2611_, 0);
                        v_isSharedCheck_2621_ =
                            (!leanh::lean_is_exclusive(v___x_2611_)) as u8;
                        if v_isSharedCheck_2621_ == 0 {
                            v___x_2616_ = v___x_2611_;
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2614_);
                            leanh::lean_dec(v___x_2611_);
                            v___x_2616_ = leanh::lean_box(0);
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2606_ == 0 {
                    v___x_2608_ = v___x_2605_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
                    v___x_2608_ = v_reuseFailAlloc_2609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2608_;
            }
            4 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2620_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2619_;
            }
            6 => {
                v___x_2626_ = leanh::lean_box(0);
                if v_isShared_2625_ == 0 {
                    leanh::lean_ctor_set(v___x_2624_, 0, v___x_2626_);
                    v___x_2628_ = v___x_2624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
                    v___x_2628_ = v_reuseFailAlloc_2629_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2628_;
            }
            8 => {
                v___x_2636_ = l_Lean_Exception_isInterrupt(v_a_2632_);
                if v___x_2636_ == 0 {
                    leanh::lean_del_object(v___x_2634_);
                    v_options_2637_ = leanh::lean_ctor_get(v___y_2587_, 2);
                    v_hasTrace_2638_ = leanh::lean_ctor_get_uint8(
                        v_options_2637_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2638_ == 0 {
                        leanh::lean_dec(v_a_2632_);
                        leanh::lean_dec_ref(v_origin_2581_);
                        v___y_2591_ = v___y_2582_;
                        v___y_2592_ = v___y_2583_;
                        v___y_2593_ = v___y_2584_;
                        v___y_2594_ = v___y_2585_;
                        v___y_2595_ = v___y_2586_;
                        v___y_2596_ = v___y_2587_;
                        v___y_2597_ = v___y_2588_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2639_ =
                            leanh::lean_ctor_get(v___y_2587_, 13);
                        v___x_2640_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__2;
                        v___x_2641_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_checkLoops___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4,
                        );
                        v___x_2642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2639_,
                            v_options_2637_,
                            v___x_2641_,
                        );
                        if v___x_2642_ == 0 {
                            leanh::lean_dec(v_a_2632_);
                            leanh::lean_dec_ref(v_origin_2581_);
                            v___y_2591_ = v___y_2582_;
                            v___y_2592_ = v___y_2583_;
                            v___y_2593_ = v___y_2584_;
                            v___y_2594_ = v___y_2585_;
                            v___y_2595_ = v___y_2586_;
                            v___y_2596_ = v___y_2587_;
                            v___y_2597_ = v___y_2588_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2643_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_2581_);
                            v_a_2644_ = leanh::lean_ctor_get(v___x_2643_, 0);
                            leanh::lean_inc(v_a_2644_);
                            leanh::lean_dec_ref(v___x_2643_);
                            v___x_2645_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__6
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once
                                ),
                                _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6,
                            );
                            v___x_2646_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                            leanh::lean_ctor_set(v___x_2646_, 1, v_a_2644_);
                            v___x_2647_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once
                                ),
                                _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8,
                            );
                            v___x_2648_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2648_, 0, v___x_2646_);
                            leanh::lean_ctor_set(v___x_2648_, 1, v___x_2647_);
                            v___x_2649_ = l_Lean_Exception_toMessageData(v_a_2632_);
                            v___x_2650_ = l_Lean_indentD(v___x_2649_);
                            v___x_2651_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2651_, 0, v___x_2648_);
                            leanh::lean_ctor_set(v___x_2651_, 1, v___x_2650_);
                            v___x_2652_ =
                                l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
                                    v___x_2640_,
                                    v___x_2651_,
                                    v___y_2585_,
                                    v___y_2586_,
                                    v___y_2587_,
                                    v___y_2588_,
                                );
                            if leanh::lean_obj_tag(v___x_2652_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2652_, 1);
                                v___y_2591_ = v___y_2582_;
                                v___y_2592_ = v___y_2583_;
                                v___y_2593_ = v___y_2584_;
                                v___y_2594_ = v___y_2585_;
                                v___y_2595_ = v___y_2586_;
                                v___y_2596_ = v___y_2587_;
                                v___y_2597_ = v___y_2588_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___y_2582_);
                                leanh::lean_dec_ref(v_thm_2580_);
                                return v___x_2652_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2582_);
                    leanh::lean_dec_ref(v_origin_2581_);
                    leanh::lean_dec_ref(v_thm_2580_);
                    if v_isShared_2635_ == 0 {
                        v___x_2654_ = v___x_2634_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2632_);
                        v___x_2654_ = v_reuseFailAlloc_2655_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__0___boxed(
    mut v___x_2657_: *mut leanh::LeanObject,
    mut v_force_2658_: *mut leanh::LeanObject,
    mut v_thm_2659_: *mut leanh::LeanObject,
    mut v_origin_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
    mut v___y_2665_: *mut leanh::LeanObject,
    mut v___y_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_force_boxed_2669_: u8 = 0;
    let mut v_res_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_force_boxed_2669_ = (leanh::lean_unbox(v_force_2658_) as u8);
    v_res_2670_ = l_Lean_Meta_Simp_checkLoops___lam__0(
        v___x_2657_,
        v_force_boxed_2669_,
        v_thm_2659_,
        v_origin_2660_,
        v___y_2661_,
        v___y_2662_,
        v___y_2663_,
        v___y_2664_,
        v___y_2665_,
        v___y_2666_,
        v___y_2667_,
    );
    leanh::lean_dec(v___y_2667_);
    leanh::lean_dec_ref(v___y_2666_);
    leanh::lean_dec(v___y_2665_);
    leanh::lean_dec_ref(v___y_2664_);
    leanh::lean_dec(v___y_2663_);
    leanh::lean_dec_ref(v___y_2662_);
    return v_res_2670_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = leanh::lean_box(0);
    v___x_2672_ = leanh::lean_unsigned_to_nat(16);
    v___x_2673_ = lean_mk_array(v___x_2672_, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2674_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0,
    );
    v___x_2675_ = leanh::lean_unsigned_to_nat(0);
    v___x_2676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2676_, 0, v___x_2675_);
    leanh::lean_ctor_set(v___x_2676_, 1, v___x_2674_);
    return v___x_2676_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2677_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2,
    );
    v___x_2679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2679_, 0, v___x_2678_);
    return v___x_2679_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = leanh::lean_unsigned_to_nat(0);
    v___x_2681_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
    );
    v___x_2682_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2682_, 0, v___x_2681_);
    leanh::lean_ctor_set(v___x_2682_, 1, v___x_2680_);
    return v___x_2682_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = leanh::lean_unsigned_to_nat(32);
    v___x_2684_ = lean_mk_empty_array_with_capacity(v___x_2683_);
    v___x_2685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2685_, 0, v___x_2684_);
    return v___x_2685_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2686_ = 5usize;
    v___x_2687_ = leanh::lean_unsigned_to_nat(0);
    v___x_2688_ = leanh::lean_unsigned_to_nat(32);
    v___x_2689_ = lean_mk_empty_array_with_capacity(v___x_2688_);
    v___x_2690_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5,
    );
    v___x_2691_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
    leanh::lean_ctor_set(v___x_2691_, 1, v___x_2689_);
    leanh::lean_ctor_set(v___x_2691_, 2, v___x_2687_);
    leanh::lean_ctor_set(v___x_2691_, 3, v___x_2687_);
    leanh::lean_ctor_set_usize(v___x_2691_, 4, v___x_2686_);
    return v___x_2691_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6,
    );
    v___x_2693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
    );
    v___x_2694_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2694_, 0, v___x_2693_);
    leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
    leanh::lean_ctor_set(v___x_2694_, 2, v___x_2693_);
    leanh::lean_ctor_set(v___x_2694_, 3, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__1(
    mut v_force_2695_: u8,
    mut v_thm_2696_: *mut leanh::LeanObject,
    mut v_origin_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: u8,
    mut v_ctxt_2699_: *mut leanh::LeanObject,
    mut v_methods_2700_: *mut leanh::LeanObject,
    mut v___xs_2701_: *mut leanh::LeanObject,
    mut v_type_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_unused_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_a_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2706_);
                leanh::lean_inc_ref(v___y_2705_);
                leanh::lean_inc(v___y_2704_);
                leanh::lean_inc_ref(v___y_2703_);
                v___x_2708_ = lean_whnf(
                    v_type_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                    v___y_2706_,
                );
                if leanh::lean_obj_tag(v___x_2708_) == 0 {
                    v_a_2709_ = leanh::lean_ctor_get(v___x_2708_, 0);
                    leanh::lean_inc(v_a_2709_);
                    leanh::lean_dec_ref_known(v___x_2708_, 1);
                    v___x_2710_ = l_Lean_Expr_appArg_x21(v_a_2709_);
                    leanh::lean_dec(v_a_2709_);
                    v___x_2711_ = leanh::lean_box((v_force_2695_) as usize);
                    v___f_2712_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Simp_checkLoops___lam__0___boxed as *mut core::ffi::c_void,
                        12,
                        4,
                    );
                    leanh::lean_closure_set(v___f_2712_, 0, v___x_2710_);
                    leanh::lean_closure_set(v___f_2712_, 1, v___x_2711_);
                    leanh::lean_closure_set(v___f_2712_, 2, v_thm_2696_);
                    leanh::lean_closure_set(v___f_2712_, 3, v_origin_2697_);
                    v___x_2713_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2714_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1,
                    );
                    v___x_2715_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
                    );
                    v___x_2716_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_2716_, 0, v___x_2714_);
                    leanh::lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2716_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_a_2698_,
                    );
                    v___x_2717_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4,
                    );
                    v___x_2718_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7,
                    );
                    v___x_2719_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v___x_2719_, 0, v___x_2716_);
                    leanh::lean_ctor_set(v___x_2719_, 1, v___x_2714_);
                    leanh::lean_ctor_set(v___x_2719_, 2, v___x_2714_);
                    leanh::lean_ctor_set(v___x_2719_, 3, v___x_2717_);
                    leanh::lean_ctor_set(v___x_2719_, 4, v___x_2713_);
                    leanh::lean_ctor_set(v___x_2719_, 5, v___x_2718_);
                    v___x_2720_ = l_Lean_Meta_Simp_SimpM_run___redArg(
                        v_ctxt_2699_,
                        v___x_2719_,
                        v_methods_2700_,
                        v___f_2712_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                        v___y_2706_,
                    );
                    if leanh::lean_obj_tag(v___x_2720_) == 0 {
                        v_isSharedCheck_2728_ =
                            (!leanh::lean_is_exclusive(v___x_2720_)) as u8;
                        if v_isSharedCheck_2728_ == 0 {
                            v_unused_2729_ = leanh::lean_ctor_get(v___x_2720_, 0);
                            leanh::lean_dec(v_unused_2729_);
                            v___x_2722_ = v___x_2720_;
                            v_isShared_2723_ = v_isSharedCheck_2728_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2720_);
                            v___x_2722_ = leanh::lean_box(0);
                            v_isShared_2723_ = v_isSharedCheck_2728_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2730_ = leanh::lean_ctor_get(v___x_2720_, 0);
                        v_isSharedCheck_2737_ =
                            (!leanh::lean_is_exclusive(v___x_2720_)) as u8;
                        if v_isSharedCheck_2737_ == 0 {
                            v___x_2732_ = v___x_2720_;
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2730_);
                            leanh::lean_dec(v___x_2720_);
                            v___x_2732_ = leanh::lean_box(0);
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_methods_2700_);
                    leanh::lean_dec_ref(v_ctxt_2699_);
                    leanh::lean_dec_ref(v_origin_2697_);
                    leanh::lean_dec_ref(v_thm_2696_);
                    v_a_2738_ = leanh::lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2745_ = (!leanh::lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2745_ == 0 {
                        v___x_2740_ = v___x_2708_;
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2738_);
                        leanh::lean_dec(v___x_2708_);
                        v___x_2740_ = leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2724_ = leanh::lean_box(0);
                if v_isShared_2723_ == 0 {
                    leanh::lean_ctor_set(v___x_2722_, 0, v___x_2724_);
                    v___x_2726_ = v___x_2722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2726_;
            }
            3 => {
                if v_isShared_2733_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2735_;
            }
            5 => {
                if v_isShared_2741_ == 0 {
                    v___x_2743_ = v___x_2740_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__1___boxed(
    mut v_force_2746_: *mut leanh::LeanObject,
    mut v_thm_2747_: *mut leanh::LeanObject,
    mut v_origin_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_ctxt_2750_: *mut leanh::LeanObject,
    mut v_methods_2751_: *mut leanh::LeanObject,
    mut v___xs_2752_: *mut leanh::LeanObject,
    mut v_type_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
    mut v___y_2755_: *mut leanh::LeanObject,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_force_boxed_2759_: u8 = 0;
    let mut v_a_25613__boxed_2760_: u8 = 0;
    let mut v_res_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_force_boxed_2759_ = (leanh::lean_unbox(v_force_2746_) as u8);
    v_a_25613__boxed_2760_ = (leanh::lean_unbox(v_a_2749_) as u8);
    v_res_2761_ = l_Lean_Meta_Simp_checkLoops___lam__1(
        v_force_boxed_2759_,
        v_thm_2747_,
        v_origin_2748_,
        v_a_25613__boxed_2760_,
        v_ctxt_2750_,
        v_methods_2751_,
        v___xs_2752_,
        v_type_2753_,
        v___y_2754_,
        v___y_2755_,
        v___y_2756_,
        v___y_2757_,
    );
    leanh::lean_dec(v___y_2757_);
    leanh::lean_dec_ref(v___y_2756_);
    leanh::lean_dec(v___y_2755_);
    leanh::lean_dec_ref(v___y_2754_);
    leanh::lean_dec_ref(v___xs_2752_);
    return v_res_2761_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops(
    mut v_force_2762_: u8,
    mut v_ctxt_2763_: *mut leanh::LeanObject,
    mut v_methods_2764_: *mut leanh::LeanObject,
    mut v_thm_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_a_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
    mut v_a_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2811_: u8 = 0;
    let mut v_a_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2771_ = l_Lean_Meta_Simp_shouldCheckLoops(
                    v_force_2762_,
                    v_ctxt_2763_,
                    v_a_2768_,
                    v_a_2769_,
                );
                if leanh::lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2811_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2811_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2811_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2772_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2774_ = leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2811_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_thm_2765_);
                    leanh::lean_dec_ref(v_methods_2764_);
                    leanh::lean_dec_ref(v_ctxt_2763_);
                    v_a_2812_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2819_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2819_ == 0 {
                        v___x_2814_ = v___x_2771_;
                        v_isShared_2815_ = v_isSharedCheck_2819_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2812_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2814_ = leanh::lean_box(0);
                        v_isShared_2815_ = v_isSharedCheck_2819_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2776_ = (leanh::lean_unbox(v_a_2772_) as u8);
                if v___x_2776_ == 0 {
                    leanh::lean_dec(v_a_2772_);
                    leanh::lean_dec_ref(v_thm_2765_);
                    leanh::lean_dec_ref(v_methods_2764_);
                    leanh::lean_dec_ref(v_ctxt_2763_);
                    v___x_2777_ = leanh::lean_box(0);
                    if v_isShared_2775_ == 0 {
                        leanh::lean_ctor_set(v___x_2774_, 0, v___x_2777_);
                        v___x_2779_ = v___x_2774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
                        v___x_2779_ = v_reuseFailAlloc_2780_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_proof_2781_ = leanh::lean_ctor_get(v_thm_2765_, 2);
                    v_origin_2782_ = leanh::lean_ctor_get(v_thm_2765_, 4);
                    leanh::lean_inc_ref(v_origin_2782_);
                    v___x_2783_ = l_Lean_Expr_hasFVar(v_proof_2781_);
                    if v___x_2783_ == 0 {
                        leanh::lean_del_object(v___x_2774_);
                        leanh::lean_inc_ref(v_thm_2765_);
                        v___x_2784_ = l_Lean_Meta_SimpTheorem_getValue(
                            v_thm_2765_,
                            v_a_2766_,
                            v_a_2767_,
                            v_a_2768_,
                            v_a_2769_,
                        );
                        if leanh::lean_obj_tag(v___x_2784_) == 0 {
                            v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                            leanh::lean_inc(v_a_2785_);
                            leanh::lean_dec_ref_known(v___x_2784_, 1);
                            leanh::lean_inc(v_a_2769_);
                            leanh::lean_inc_ref(v_a_2768_);
                            leanh::lean_inc(v_a_2767_);
                            leanh::lean_inc_ref(v_a_2766_);
                            v___x_2786_ = lean_infer_type(
                                v_a_2785_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
                            );
                            if leanh::lean_obj_tag(v___x_2786_) == 0 {
                                v_a_2787_ = leanh::lean_ctor_get(v___x_2786_, 0);
                                leanh::lean_inc(v_a_2787_);
                                leanh::lean_dec_ref_known(v___x_2786_, 1);
                                v___x_2788_ = leanh::lean_box((v_force_2762_) as usize);
                                v___f_2789_ = leanh::lean_alloc_closure(
                                    l_Lean_Meta_Simp_checkLoops___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    6,
                                );
                                leanh::lean_closure_set(v___f_2789_, 0, v___x_2788_);
                                leanh::lean_closure_set(v___f_2789_, 1, v_thm_2765_);
                                leanh::lean_closure_set(v___f_2789_, 2, v_origin_2782_);
                                leanh::lean_closure_set(v___f_2789_, 3, v_a_2772_);
                                leanh::lean_closure_set(v___f_2789_, 4, v_ctxt_2763_);
                                leanh::lean_closure_set(v___f_2789_, 5, v_methods_2764_);
                                v___x_2790_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_2787_, v___f_2789_, v___x_2783_, v___x_2783_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
                                return v___x_2790_;
                            } else {
                                leanh::lean_dec_ref(v_origin_2782_);
                                leanh::lean_dec(v_a_2772_);
                                leanh::lean_dec_ref(v_thm_2765_);
                                leanh::lean_dec_ref(v_methods_2764_);
                                leanh::lean_dec_ref(v_ctxt_2763_);
                                v_a_2791_ = leanh::lean_ctor_get(v___x_2786_, 0);
                                v_isSharedCheck_2798_ =
                                    (!leanh::lean_is_exclusive(v___x_2786_)) as u8;
                                if v_isSharedCheck_2798_ == 0 {
                                    v___x_2793_ = v___x_2786_;
                                    v_isShared_2794_ = v_isSharedCheck_2798_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2791_);
                                    leanh::lean_dec(v___x_2786_);
                                    v___x_2793_ = leanh::lean_box(0);
                                    v_isShared_2794_ = v_isSharedCheck_2798_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_origin_2782_);
                            leanh::lean_dec(v_a_2772_);
                            leanh::lean_dec_ref(v_thm_2765_);
                            leanh::lean_dec_ref(v_methods_2764_);
                            leanh::lean_dec_ref(v_ctxt_2763_);
                            v_a_2799_ = leanh::lean_ctor_get(v___x_2784_, 0);
                            v_isSharedCheck_2806_ =
                                (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2784_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2799_);
                                leanh::lean_dec(v___x_2784_);
                                v___x_2801_ = leanh::lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_origin_2782_);
                        leanh::lean_dec(v_a_2772_);
                        leanh::lean_dec_ref(v_thm_2765_);
                        leanh::lean_dec_ref(v_methods_2764_);
                        leanh::lean_dec_ref(v_ctxt_2763_);
                        v___x_2807_ = leanh::lean_box(0);
                        if v_isShared_2775_ == 0 {
                            leanh::lean_ctor_set(v___x_2774_, 0, v___x_2807_);
                            v___x_2809_ = v___x_2774_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2810_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
                            v___x_2809_ = v_reuseFailAlloc_2810_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2779_;
            }
            3 => {
                if v_isShared_2794_ == 0 {
                    v___x_2796_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2796_;
            }
            5 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2804_;
            }
            7 => {
                return v___x_2809_;
            }
            8 => {
                if v_isShared_2815_ == 0 {
                    v___x_2817_ = v___x_2814_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
                    v___x_2817_ = v_reuseFailAlloc_2818_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___boxed(
    mut v_force_2820_: *mut leanh::LeanObject,
    mut v_ctxt_2821_: *mut leanh::LeanObject,
    mut v_methods_2822_: *mut leanh::LeanObject,
    mut v_thm_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_force_boxed_2829_: u8 = 0;
    let mut v_res_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_force_boxed_2829_ = (leanh::lean_unbox(v_force_2820_) as u8);
    v_res_2830_ = l_Lean_Meta_Simp_checkLoops(
        v_force_boxed_2829_,
        v_ctxt_2821_,
        v_methods_2822_,
        v_thm_2823_,
        v_a_2824_,
        v_a_2825_,
        v_a_2826_,
        v_a_2827_,
    );
    leanh::lean_dec(v_a_2827_);
    leanh::lean_dec_ref(v_a_2826_);
    leanh::lean_dec(v_a_2825_);
    leanh::lean_dec_ref(v_a_2824_);
    return v_res_2830_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(
    mut v_cls_2831_: *mut leanh::LeanObject,
    mut v_msg_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
    mut v___y_2835_: *mut leanh::LeanObject,
    mut v___y_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
        v_cls_2831_,
        v_msg_2832_,
        v___y_2836_,
        v___y_2837_,
        v___y_2838_,
        v___y_2839_,
    );
    return v___x_2841_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(
    mut v_cls_2842_: *mut leanh::LeanObject,
    mut v_msg_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
    mut v___y_2845_: *mut leanh::LeanObject,
    mut v___y_2846_: *mut leanh::LeanObject,
    mut v___y_2847_: *mut leanh::LeanObject,
    mut v___y_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(
        v_cls_2842_,
        v_msg_2843_,
        v___y_2844_,
        v___y_2845_,
        v___y_2846_,
        v___y_2847_,
        v___y_2848_,
        v___y_2849_,
        v___y_2850_,
    );
    leanh::lean_dec(v___y_2850_);
    leanh::lean_dec_ref(v___y_2849_);
    leanh::lean_dec(v___y_2848_);
    leanh::lean_dec_ref(v___y_2847_);
    leanh::lean_dec(v___y_2846_);
    leanh::lean_dec_ref(v___y_2845_);
    leanh::lean_dec(v___y_2844_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(
    mut v_ref_2853_: *mut leanh::LeanObject,
    mut v_msgData_2854_: *mut leanh::LeanObject,
    mut v_severity_2855_: u8,
    mut v_isSilent_2856_: u8,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
    mut v___y_2859_: *mut leanh::LeanObject,
    mut v___y_2860_: *mut leanh::LeanObject,
    mut v___y_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2853_, v_msgData_2854_, v_severity_2855_, v_isSilent_2856_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
    return v___x_2865_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(
    mut v_ref_2866_: *mut leanh::LeanObject,
    mut v_msgData_2867_: *mut leanh::LeanObject,
    mut v_severity_2868_: *mut leanh::LeanObject,
    mut v_isSilent_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2878_: u8 = 0;
    let mut v_isSilent_boxed_2879_: u8 = 0;
    let mut v_res_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2878_ = (leanh::lean_unbox(v_severity_2868_) as u8);
    v_isSilent_boxed_2879_ = (leanh::lean_unbox(v_isSilent_2869_) as u8);
    v_res_2880_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_2866_, v_msgData_2867_, v_severity_boxed_2878_, v_isSilent_boxed_2879_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
    leanh::lean_dec(v___y_2876_);
    leanh::lean_dec_ref(v___y_2875_);
    leanh::lean_dec(v___y_2874_);
    leanh::lean_dec_ref(v___y_2873_);
    leanh::lean_dec(v___y_2872_);
    leanh::lean_dec_ref(v___y_2871_);
    leanh::lean_dec(v___y_2870_);
    leanh::lean_dec(v_ref_2866_);
    return v_res_2880_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Simp_linter_loopingSimpArgs = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Simp_linter_loopingSimpArgs);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_LoopProtection(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
}