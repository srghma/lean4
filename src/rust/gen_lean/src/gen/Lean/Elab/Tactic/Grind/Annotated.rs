// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Annotated
// Imports: Lean.Elab.Command Init.Grind.Annotated Std.Time.Format
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Grind::Annotated::{
    initialize_Init_Grind_Annotated, runtime_initialize_Init_Grind_Annotated,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getString;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_getRef___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_header, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Std::Time::Format::{
    initialize_Std_Time_Format, l_Std_Time_PlainDate_parse, runtime_initialize_Std_Time_Format,
};
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4907018543776028915 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 110, 110, 111, 116, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16829015557389976567 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5616972686803082506 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2256150756833274379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3276352215072587485 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11718449169950160452 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,639376851334178974 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 65, 110, 110, 111, 116, 97, 116, 101, 100, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8145800002992544803 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [103, 114, 105, 110, 100, 65, 110, 110, 111, 116, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value) as *mut leanh::LeanObject,10959305042798744005 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 100, 97, 116, 101, 32, 102, 111, 114, 109, 97, 116, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [10, 69, 120, 112, 101, 99, 116, 101, 100, 32, 102, 111, 114, 109, 97, 116, 58, 32, 89, 89, 89, 89, 45, 77, 77, 45, 68, 68, 32, 40, 101, 46, 103, 46, 44, 32, 34, 50, 48, 50, 53, 45, 48, 49, 45, 49, 53, 34, 41, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 71, 114, 105, 110, 100, 65, 110, 110, 111, 116, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value) as *mut leanh::LeanObject,8158861494599483108 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(
    mut v_es_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_array_mk(v_es_451_);
    return v___x_452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(
    mut v_as_453_: *mut leanh::LeanObject,
    mut v_i_454_: usize,
    mut v_stop_455_: usize,
    mut v_b_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: usize = 0;
    let mut v___x_461_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_457_ = lean_usize_dec_eq(v_i_454_, v_stop_455_);
                if v___x_457_ == 0 {
                    v___x_458_ = lean_array_uget_borrowed(v_as_453_, v_i_454_);
                    leanh::lean_inc(v___x_458_);
                    v___x_459_ = l_Lean_NameSet_insert(v_b_456_, v___x_458_);
                    v___x_460_ = 1usize;
                    v___x_461_ = lean_usize_add(v_i_454_, v___x_460_);
                    v_i_454_ = v___x_461_;
                    v_b_456_ = v___x_459_;
                    state = 0;
                    continue;
                } else {
                    return v_b_456_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_463_: *mut leanh::LeanObject,
    mut v_i_464_: *mut leanh::LeanObject,
    mut v_stop_465_: *mut leanh::LeanObject,
    mut v_b_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_467_: usize = 0;
    let mut v_stop_boxed_468_: usize = 0;
    let mut v_res_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_467_ = leanh::lean_unbox_usize(v_i_464_);
    leanh::lean_dec(v_i_464_);
    v_stop_boxed_468_ = leanh::lean_unbox_usize(v_stop_465_);
    leanh::lean_dec(v_stop_465_);
    v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(v_as_463_, v_i_boxed_467_, v_stop_boxed_468_, v_b_466_);
    leanh::lean_dec_ref(v_as_463_);
    return v_res_469_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(
    mut v_as_470_: *mut leanh::LeanObject,
    mut v_i_471_: usize,
    mut v_stop_472_: usize,
    mut v_b_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: usize = 0;
    let mut v___x_477_: usize = 0;
    let mut v___x_479_: u8 = 0;
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: u8 = 0;
    let mut v___x_484_: u8 = 0;
    let mut v___x_485_: usize = 0;
    let mut v___x_486_: usize = 0;
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: usize = 0;
    let mut v___x_489_: usize = 0;
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_479_ = lean_usize_dec_eq(v_i_471_, v_stop_472_);
                if v___x_479_ == 0 {
                    v___x_480_ = leanh::lean_unsigned_to_nat(0);
                    v___x_481_ = lean_array_uget_borrowed(v_as_470_, v_i_471_);
                    v___x_482_ = lean_array_get_size(v___x_481_);
                    v___x_483_ = lean_nat_dec_lt(v___x_480_, v___x_482_);
                    if v___x_483_ == 0 {
                        v___y_475_ = v_b_473_;
                        state = 1;
                        continue;
                    } else {
                        v___x_484_ = lean_nat_dec_le(v___x_482_, v___x_482_);
                        if v___x_484_ == 0 {
                            if v___x_483_ == 0 {
                                v___y_475_ = v_b_473_;
                                state = 1;
                                continue;
                            } else {
                                v___x_485_ = 0usize;
                                v___x_486_ = lean_usize_of_nat(v___x_482_);
                                v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(v___x_481_, v___x_485_, v___x_486_, v_b_473_);
                                v___y_475_ = v___x_487_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_488_ = 0usize;
                            v___x_489_ = lean_usize_of_nat(v___x_482_);
                            v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(v___x_481_, v___x_488_, v___x_489_, v_b_473_);
                            v___y_475_ = v___x_490_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_473_;
                }
            }
            1 => {
                v___x_476_ = 1usize;
                v___x_477_ = lean_usize_add(v_i_471_, v___x_476_);
                v_i_471_ = v___x_477_;
                v_b_473_ = v___y_475_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_491_: *mut leanh::LeanObject,
    mut v_i_492_: *mut leanh::LeanObject,
    mut v_stop_493_: *mut leanh::LeanObject,
    mut v_b_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_495_: usize = 0;
    let mut v_stop_boxed_496_: usize = 0;
    let mut v_res_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_495_ = leanh::lean_unbox_usize(v_i_492_);
    leanh::lean_dec(v_i_492_);
    v_stop_boxed_496_ = leanh::lean_unbox_usize(v_stop_493_);
    leanh::lean_dec(v_stop_493_);
    v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(v_as_491_, v_i_boxed_495_, v_stop_boxed_496_, v_b_494_);
    leanh::lean_dec_ref(v_as_491_);
    return v_res_497_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(
    mut v___x_498_: *mut leanh::LeanObject,
    mut v_entries_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    v___x_500_ = l_Lean_NameSet_empty;
    v___x_501_ = lean_array_get_size(v_entries_499_);
    v___x_502_ = lean_nat_dec_lt(v___x_498_, v___x_501_);
    if v___x_502_ == 0 {
        return v___x_500_;
    } else {
        let mut v___x_503_: u8 = 0;
        v___x_503_ = lean_nat_dec_le(v___x_501_, v___x_501_);
        if v___x_503_ == 0 {
            if v___x_502_ == 0 {
                return v___x_500_;
            } else {
                let mut v___x_504_: usize = 0;
                let mut v___x_505_: usize = 0;
                let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_504_ = 0usize;
                v___x_505_ = lean_usize_of_nat(v___x_501_);
                v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(v_entries_499_, v___x_504_, v___x_505_, v___x_500_);
                return v___x_506_;
            }
        } else {
            let mut v___x_507_: usize = 0;
            let mut v___x_508_: usize = 0;
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_507_ = 0usize;
            v___x_508_ = lean_usize_of_nat(v___x_501_);
            v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(v_entries_499_, v___x_507_, v___x_508_, v___x_500_);
            return v___x_509_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(
    mut v___x_510_: *mut leanh::LeanObject,
    mut v_entries_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_512_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(v___x_510_, v_entries_511_);
    leanh::lean_dec_ref(v_entries_511_);
    leanh::lean_dec(v___x_510_);
    return v_res_512_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_;
    v___x_569_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_568_);
    return v___x_569_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(
    mut v_a_570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_();
    return v_res_571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(
    mut v_env_572_: *mut leanh::LeanObject,
    mut v_modIdx_573_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleName_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    v___x_574_ =
        l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
    v_toEnvExtension_575_ = leanh::lean_ctor_get(v___x_574_, 0);
    v_asyncMode_576_ = leanh::lean_ctor_get(v_toEnvExtension_575_, 2);
    v___x_577_ = leanh::lean_box(1);
    v___x_578_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_env_572_);
    v_state_579_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_577_,
        v___x_574_,
        v_env_572_,
        v_asyncMode_576_,
        v___x_578_,
    );
    v___x_580_ = l_Lean_Environment_header(v_env_572_);
    leanh::lean_dec_ref(v_env_572_);
    v___x_581_ = l_Lean_EnvironmentHeader_moduleNames(v___x_580_);
    v_moduleName_582_ = lean_array_get(v___x_578_, v___x_581_, v_modIdx_573_);
    leanh::lean_dec_ref(v___x_581_);
    v___x_583_ = l_Lean_NameSet_contains(v_state_579_, v_moduleName_582_);
    leanh::lean_dec(v_moduleName_582_);
    leanh::lean_dec(v_state_579_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule___boxed(
    mut v_env_584_: *mut leanh::LeanObject,
    mut v_modIdx_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_586_: u8 = 0;
    let mut v_r_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_586_ = l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(v_env_584_, v_modIdx_585_);
    leanh::lean_dec(v_modIdx_585_);
    v_r_587_ = leanh::lean_box((v_res_586_) as usize);
    return v_r_587_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = leanh::lean_box(0);
    v___x_589_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_590_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_590_, 0, v___x_589_);
    leanh::lean_ctor_set(v___x_590_, 1, v___x_588_);
    return v___x_590_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0);
    v___x_593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_593_, 0, v___x_592_);
    return v___x_593_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___boxed(
    mut v___y_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
    return v_res_595_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0(
    mut v_00_u03b1_596_: *mut leanh::LeanObject,
    mut v___y_597_: *mut leanh::LeanObject,
    mut v___y_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
    return v___x_600_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___boxed(
    mut v_00_u03b1_601_: *mut leanh::LeanObject,
    mut v___y_602_: *mut leanh::LeanObject,
    mut v___y_603_: *mut leanh::LeanObject,
    mut v___y_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_605_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0(v_00_u03b1_601_, v___y_602_, v___y_603_);
    leanh::lean_dec(v___y_603_);
    leanh::lean_dec_ref(v___y_602_);
    return v_res_605_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(
    mut v___y_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_st_ref_get(v___y_606_);
    v_env_609_ = leanh::lean_ctor_get(v___x_608_, 0);
    leanh::lean_inc_ref(v_env_609_);
    leanh::lean_dec(v___x_608_);
    v___x_610_ = l_Lean_Environment_header(v_env_609_);
    leanh::lean_dec_ref(v_env_609_);
    v_mainModule_611_ = leanh::lean_ctor_get(v___x_610_, 0);
    leanh::lean_inc(v_mainModule_611_);
    leanh::lean_dec_ref(v___x_610_);
    v___x_612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_612_, 0, v_mainModule_611_);
    return v___x_612_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg___boxed(
    mut v___y_613_: *mut leanh::LeanObject,
    mut v___y_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(v___y_613_);
    leanh::lean_dec(v___y_613_);
    return v_res_615_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2(
    mut v___y_616_: *mut leanh::LeanObject,
    mut v___y_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(v___y_617_);
    return v___x_619_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___boxed(
    mut v___y_620_: *mut leanh::LeanObject,
    mut v___y_621_: *mut leanh::LeanObject,
    mut v___y_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_623_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2(v___y_620_, v___y_621_);
    leanh::lean_dec(v___y_621_);
    leanh::lean_dec_ref(v___y_620_);
    return v_res_623_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = leanh::lean_box(1);
    v___x_625_ = l_Lean_MessageData_ofFormat(v___x_624_);
    return v___x_625_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2;
    v___x_630_ = l_Lean_MessageData_ofFormat(v___x_629_);
    return v___x_630_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(
    mut v_x_631_: *mut leanh::LeanObject,
    mut v_x_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v_before_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_unused_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_632_) == 0 {
                    return v_x_631_;
                } else {
                    v_head_633_ = leanh::lean_ctor_get(v_x_632_, 0);
                    v_tail_634_ = leanh::lean_ctor_get(v_x_632_, 1);
                    v_isSharedCheck_656_ = (!leanh::lean_is_exclusive(v_x_632_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_636_ = v_x_632_;
                        v_isShared_637_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_634_);
                        leanh::lean_inc(v_head_633_);
                        leanh::lean_dec(v_x_632_);
                        v___x_636_ = leanh::lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_638_ = leanh::lean_ctor_get(v_head_633_, 0);
                v_isSharedCheck_654_ = (!leanh::lean_is_exclusive(v_head_633_)) as u8;
                if v_isSharedCheck_654_ == 0 {
                    v_unused_655_ = leanh::lean_ctor_get(v_head_633_, 1);
                    leanh::lean_dec(v_unused_655_);
                    v___x_640_ = v_head_633_;
                    v_isShared_641_ = v_isSharedCheck_654_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_638_);
                    leanh::lean_dec(v_head_633_);
                    v___x_640_ = leanh::lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_641_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_640_, 7);
                    leanh::lean_ctor_set(v___x_640_, 1, v___x_642_);
                    leanh::lean_ctor_set(v___x_640_, 0, v_x_631_);
                    v___x_644_ = v___x_640_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_x_631_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_642_);
                    v___x_644_ = v_reuseFailAlloc_653_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_645_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3);
                if v_isShared_637_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_636_, 7);
                    leanh::lean_ctor_set(v___x_636_, 1, v___x_645_);
                    leanh::lean_ctor_set(v___x_636_, 0, v___x_644_);
                    v___x_647_ = v___x_636_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_645_);
                    v___x_647_ = v_reuseFailAlloc_652_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_648_ = l_Lean_MessageData_ofSyntax(v_before_638_);
                v___x_649_ = l_Lean_indentD(v___x_648_);
                v___x_650_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_650_, 0, v___x_647_);
                leanh::lean_ctor_set(v___x_650_, 1, v___x_649_);
                v_x_631_ = v___x_650_;
                v_x_632_ = v_tail_634_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(
    mut v_opts_657_: *mut leanh::LeanObject,
    mut v_opt_658_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_659_ = leanh::lean_ctor_get(v_opt_658_, 0);
    v_defValue_660_ = leanh::lean_ctor_get(v_opt_658_, 1);
    v_map_661_ = leanh::lean_ctor_get(v_opts_657_, 0);
    v___x_662_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_661_,
            v_name_659_,
        );
    if leanh::lean_obj_tag(v___x_662_) == 0 {
        let mut v___x_663_: u8 = 0;
        v___x_663_ = (leanh::lean_unbox(v_defValue_660_) as u8);
        return v___x_663_;
    } else {
        let mut v_val_664_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_664_ = leanh::lean_ctor_get(v___x_662_, 0);
        leanh::lean_inc(v_val_664_);
        leanh::lean_dec_ref_known(v___x_662_, 1);
        if leanh::lean_obj_tag(v_val_664_) == 1 {
            let mut v_v_665_: u8 = 0;
            v_v_665_ = leanh::lean_ctor_get_uint8(v_val_664_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_664_, 0);
            return v_v_665_;
        } else {
            let mut v___x_666_: u8 = 0;
            leanh::lean_dec(v_val_664_);
            v___x_666_ = (leanh::lean_unbox(v_defValue_660_) as u8);
            return v___x_666_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4___boxed(
    mut v_opts_667_: *mut leanh::LeanObject,
    mut v_opt_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_669_: u8 = 0;
    let mut v_r_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(v_opts_667_, v_opt_668_);
    leanh::lean_dec_ref(v_opt_668_);
    leanh::lean_dec_ref(v_opts_667_);
    v_r_670_ = leanh::lean_box((v_res_669_) as usize);
    return v_r_670_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_674_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1;
    v___x_675_ = l_Lean_MessageData_ofFormat(v___x_674_);
    return v___x_675_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(
    mut v_msgData_676_: *mut leanh::LeanObject,
    mut v_macroStack_677_: *mut leanh::LeanObject,
    mut v___y_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_693_: u8 = 0;
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_705_: u8 = 0;
    let mut v_unused_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_680_ = lean_st_ref_get(v___y_678_);
                v_scopes_681_ = leanh::lean_ctor_get(v___x_680_, 2);
                leanh::lean_inc(v_scopes_681_);
                leanh::lean_dec(v___x_680_);
                v___x_682_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_683_ = l_List_head_x21___redArg(v___x_682_, v_scopes_681_);
                leanh::lean_dec(v_scopes_681_);
                v_opts_684_ = leanh::lean_ctor_get(v___x_683_, 1);
                leanh::lean_inc_ref(v_opts_684_);
                leanh::lean_dec(v___x_683_);
                v___x_685_ = l_Lean_Elab_pp_macroStack;
                v___x_686_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(v_opts_684_, v___x_685_);
                leanh::lean_dec_ref(v_opts_684_);
                if v___x_686_ == 0 {
                    leanh::lean_dec(v_macroStack_677_);
                    v___x_687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_687_, 0, v_msgData_676_);
                    return v___x_687_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_677_) == 0 {
                        v___x_688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_688_, 0, v_msgData_676_);
                        return v___x_688_;
                    } else {
                        v_head_689_ = leanh::lean_ctor_get(v_macroStack_677_, 0);
                        leanh::lean_inc(v_head_689_);
                        v_after_690_ = leanh::lean_ctor_get(v_head_689_, 1);
                        v_isSharedCheck_705_ =
                            (!leanh::lean_is_exclusive(v_head_689_)) as u8;
                        if v_isSharedCheck_705_ == 0 {
                            v_unused_706_ = leanh::lean_ctor_get(v_head_689_, 0);
                            leanh::lean_dec(v_unused_706_);
                            v___x_692_ = v_head_689_;
                            v_isShared_693_ = v_isSharedCheck_705_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_690_);
                            leanh::lean_dec(v_head_689_);
                            v___x_692_ = leanh::lean_box(0);
                            v_isShared_693_ = v_isSharedCheck_705_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_693_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_692_, 7);
                    leanh::lean_ctor_set(v___x_692_, 1, v___x_694_);
                    leanh::lean_ctor_set(v___x_692_, 0, v_msgData_676_);
                    v___x_696_ = v___x_692_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_704_, 0, v_msgData_676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_694_);
                    v___x_696_ = v_reuseFailAlloc_704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_697_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2);
                v___x_698_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_698_, 0, v___x_696_);
                leanh::lean_ctor_set(v___x_698_, 1, v___x_697_);
                v___x_699_ = l_Lean_MessageData_ofSyntax(v_after_690_);
                v___x_700_ = l_Lean_indentD(v___x_699_);
                v_msgData_701_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_701_, 0, v___x_698_);
                leanh::lean_ctor_set(v_msgData_701_, 1, v___x_700_);
                v___x_702_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(v_msgData_701_, v_macroStack_677_);
                v___x_703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_703_, 0, v___x_702_);
                return v___x_703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___boxed(
    mut v_msgData_707_: *mut leanh::LeanObject,
    mut v_macroStack_708_: *mut leanh::LeanObject,
    mut v___y_709_: *mut leanh::LeanObject,
    mut v___y_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_711_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(v_msgData_707_, v_macroStack_708_, v___y_709_);
    leanh::lean_dec(v___y_709_);
    return v_res_711_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0);
    v___x_714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_714_, 0, v___x_713_);
    return v___x_714_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1);
    v___x_716_ = leanh::lean_unsigned_to_nat(0);
    v___x_717_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_717_, 0, v___x_716_);
    leanh::lean_ctor_set(v___x_717_, 1, v___x_716_);
    leanh::lean_ctor_set(v___x_717_, 2, v___x_716_);
    leanh::lean_ctor_set(v___x_717_, 3, v___x_716_);
    leanh::lean_ctor_set(v___x_717_, 4, v___x_715_);
    leanh::lean_ctor_set(v___x_717_, 5, v___x_715_);
    leanh::lean_ctor_set(v___x_717_, 6, v___x_715_);
    leanh::lean_ctor_set(v___x_717_, 7, v___x_715_);
    leanh::lean_ctor_set(v___x_717_, 8, v___x_715_);
    leanh::lean_ctor_set(v___x_717_, 9, v___x_715_);
    return v___x_717_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = leanh::lean_unsigned_to_nat(32);
    v___x_719_ = lean_mk_empty_array_with_capacity(v___x_718_);
    v___x_720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_720_, 0, v___x_719_);
    return v___x_720_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_721_: usize = 0;
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = 5usize;
    v___x_722_ = leanh::lean_unsigned_to_nat(0);
    v___x_723_ = leanh::lean_unsigned_to_nat(32);
    v___x_724_ = lean_mk_empty_array_with_capacity(v___x_723_);
    v___x_725_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3);
    v___x_726_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_726_, 0, v___x_725_);
    leanh::lean_ctor_set(v___x_726_, 1, v___x_724_);
    leanh::lean_ctor_set(v___x_726_, 2, v___x_722_);
    leanh::lean_ctor_set(v___x_726_, 3, v___x_722_);
    leanh::lean_ctor_set_usize(v___x_726_, 4, v___x_721_);
    return v___x_726_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = leanh::lean_box(1);
    v___x_728_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4);
    v___x_729_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1);
    v___x_730_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
    leanh::lean_ctor_set(v___x_730_, 1, v___x_728_);
    leanh::lean_ctor_set(v___x_730_, 2, v___x_727_);
    return v___x_730_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(
    mut v_msgData_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = lean_st_ref_get(v___y_732_);
    v_env_735_ = leanh::lean_ctor_get(v___x_734_, 0);
    leanh::lean_inc_ref(v_env_735_);
    leanh::lean_dec(v___x_734_);
    v___x_736_ = lean_st_ref_get(v___y_732_);
    v_scopes_737_ = leanh::lean_ctor_get(v___x_736_, 2);
    leanh::lean_inc(v_scopes_737_);
    leanh::lean_dec(v___x_736_);
    v___x_738_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_739_ = l_List_head_x21___redArg(v___x_738_, v_scopes_737_);
    leanh::lean_dec(v_scopes_737_);
    v_opts_740_ = leanh::lean_ctor_get(v___x_739_, 1);
    leanh::lean_inc_ref(v_opts_740_);
    leanh::lean_dec(v___x_739_);
    v___x_741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2);
    v___x_742_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5);
    v___x_743_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_743_, 0, v_env_735_);
    leanh::lean_ctor_set(v___x_743_, 1, v___x_741_);
    leanh::lean_ctor_set(v___x_743_, 2, v___x_742_);
    leanh::lean_ctor_set(v___x_743_, 3, v_opts_740_);
    v___x_744_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_744_, 0, v___x_743_);
    leanh::lean_ctor_set(v___x_744_, 1, v_msgData_731_);
    v___x_745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_745_, 0, v___x_744_);
    return v___x_745_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___boxed(
    mut v_msgData_746_: *mut leanh::LeanObject,
    mut v___y_747_: *mut leanh::LeanObject,
    mut v___y_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(v_msgData_746_, v___y_747_);
    leanh::lean_dec(v___y_747_);
    return v_res_749_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(
    mut v_msg_750_: *mut leanh::LeanObject,
    mut v___y_751_: *mut leanh::LeanObject,
    mut v___y_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_a_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_754_ = l_Lean_Elab_Command_getRef___redArg(v___y_751_);
                if leanh::lean_obj_tag(v___x_754_) == 0 {
                    v_a_755_ = leanh::lean_ctor_get(v___x_754_, 0);
                    leanh::lean_inc(v_a_755_);
                    leanh::lean_dec_ref_known(v___x_754_, 1);
                    v_macroStack_756_ = leanh::lean_ctor_get(v___y_751_, 4);
                    v___x_757_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(v_msg_750_, v___y_752_);
                    v_a_758_ = leanh::lean_ctor_get(v___x_757_, 0);
                    leanh::lean_inc(v_a_758_);
                    leanh::lean_dec_ref(v___x_757_);
                    v___x_759_ = l_Lean_Elab_getBetterRef(v_a_755_, v_macroStack_756_);
                    leanh::lean_dec(v_a_755_);
                    leanh::lean_inc(v_macroStack_756_);
                    v___x_760_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(v_a_758_, v_macroStack_756_, v___y_752_);
                    v_a_761_ = leanh::lean_ctor_get(v___x_760_, 0);
                    v_isSharedCheck_769_ = (!leanh::lean_is_exclusive(v___x_760_)) as u8;
                    if v_isSharedCheck_769_ == 0 {
                        v___x_763_ = v___x_760_;
                        v_isShared_764_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_761_);
                        leanh::lean_dec(v___x_760_);
                        v___x_763_ = leanh::lean_box(0);
                        v_isShared_764_ = v_isSharedCheck_769_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_750_);
                    v_a_770_ = leanh::lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_777_ = (!leanh::lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_777_ == 0 {
                        v___x_772_ = v___x_754_;
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_770_);
                        leanh::lean_dec(v___x_754_);
                        v___x_772_ = leanh::lean_box(0);
                        v_isShared_773_ = v_isSharedCheck_777_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_765_, 0, v___x_759_);
                leanh::lean_ctor_set(v___x_765_, 1, v_a_761_);
                if v_isShared_764_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_763_, 1);
                    leanh::lean_ctor_set(v___x_763_, 0, v___x_765_);
                    v___x_767_ = v___x_763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
                    v___x_767_ = v_reuseFailAlloc_768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_767_;
            }
            3 => {
                if v_isShared_773_ == 0 {
                    v___x_775_ = v___x_772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
                    v___x_775_ = v_reuseFailAlloc_776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg___boxed(
    mut v_msg_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
    mut v___y_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(v_msg_778_, v___y_779_, v___y_780_);
    leanh::lean_dec(v___y_780_);
    leanh::lean_dec_ref(v___y_779_);
    return v_res_782_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4;
    v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
    return v___x_793_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6;
    v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
    return v___x_796_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated(
    mut v_stx_797_: *mut leanh::LeanObject,
    mut v_a_798_: *mut leanh::LeanObject,
    mut v_a_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateStr_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateValue_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_834_: u8 = 0;
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut v_isSharedCheck_849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_801_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3;
                leanh::lean_inc(v_stx_797_);
                v___x_802_ = l_Lean_Syntax_isOfKind(v_stx_797_, v___x_801_);
                if v___x_802_ == 0 {
                    leanh::lean_dec(v_stx_797_);
                    v___x_803_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
                    return v___x_803_;
                } else {
                    v___x_804_ = leanh::lean_unsigned_to_nat(1);
                    v_dateStr_805_ = l_Lean_Syntax_getArg(v_stx_797_, v___x_804_);
                    leanh::lean_dec(v_stx_797_);
                    v_dateValue_806_ = l_Lean_TSyntax_getString(v_dateStr_805_);
                    leanh::lean_dec(v_dateStr_805_);
                    v___x_807_ = l_Std_Time_PlainDate_parse(v_dateValue_806_);
                    if leanh::lean_obj_tag(v___x_807_) == 0 {
                        v_a_808_ = leanh::lean_ctor_get(v___x_807_, 0);
                        leanh::lean_inc(v_a_808_);
                        leanh::lean_dec_ref_known(v___x_807_, 1);
                        v___x_809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5);
                        v___x_810_ = l_Lean_stringToMessageData(v_a_808_);
                        v___x_811_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_811_, 0, v___x_809_);
                        leanh::lean_ctor_set(v___x_811_, 1, v___x_810_);
                        v___x_812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7_once), _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7);
                        v___x_813_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_813_, 0, v___x_811_);
                        leanh::lean_ctor_set(v___x_813_, 1, v___x_812_);
                        v___x_814_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(v___x_813_, v_a_798_, v_a_799_);
                        return v___x_814_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_807_, 1);
                        v___x_815_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(v_a_799_);
                        v_a_816_ = leanh::lean_ctor_get(v___x_815_, 0);
                        v_isSharedCheck_849_ = (!leanh::lean_is_exclusive(v___x_815_)) as u8;
                        if v_isSharedCheck_849_ == 0 {
                            v___x_818_ = v___x_815_;
                            v_isShared_819_ = v_isSharedCheck_849_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_816_);
                            leanh::lean_dec(v___x_815_);
                            v___x_818_ = leanh::lean_box(0);
                            v_isShared_819_ = v_isSharedCheck_849_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_820_ = lean_st_ref_take(v_a_799_);
                v_env_821_ = leanh::lean_ctor_get(v___x_820_, 0);
                v_messages_822_ = leanh::lean_ctor_get(v___x_820_, 1);
                v_scopes_823_ = leanh::lean_ctor_get(v___x_820_, 2);
                v_usedQuotCtxts_824_ = leanh::lean_ctor_get(v___x_820_, 3);
                v_nextMacroScope_825_ = leanh::lean_ctor_get(v___x_820_, 4);
                v_maxRecDepth_826_ = leanh::lean_ctor_get(v___x_820_, 5);
                v_ngen_827_ = leanh::lean_ctor_get(v___x_820_, 6);
                v_auxDeclNGen_828_ = leanh::lean_ctor_get(v___x_820_, 7);
                v_infoState_829_ = leanh::lean_ctor_get(v___x_820_, 8);
                v_traceState_830_ = leanh::lean_ctor_get(v___x_820_, 9);
                v_snapshotTasks_831_ = leanh::lean_ctor_get(v___x_820_, 10);
                v_isSharedCheck_848_ = (!leanh::lean_is_exclusive(v___x_820_)) as u8;
                if v_isSharedCheck_848_ == 0 {
                    v___x_833_ = v___x_820_;
                    v_isShared_834_ = v_isSharedCheck_848_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_831_);
                    leanh::lean_inc(v_traceState_830_);
                    leanh::lean_inc(v_infoState_829_);
                    leanh::lean_inc(v_auxDeclNGen_828_);
                    leanh::lean_inc(v_ngen_827_);
                    leanh::lean_inc(v_maxRecDepth_826_);
                    leanh::lean_inc(v_nextMacroScope_825_);
                    leanh::lean_inc(v_usedQuotCtxts_824_);
                    leanh::lean_inc(v_scopes_823_);
                    leanh::lean_inc(v_messages_822_);
                    leanh::lean_inc(v_env_821_);
                    leanh::lean_dec(v___x_820_);
                    v___x_833_ = leanh::lean_box(0);
                    v_isShared_834_ = v_isSharedCheck_848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_835_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
                v_toEnvExtension_836_ = leanh::lean_ctor_get(v___x_835_, 0);
                v_asyncMode_837_ = leanh::lean_ctor_get(v_toEnvExtension_836_, 2);
                v___x_838_ = leanh::lean_box(0);
                v___x_839_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_835_,
                    v_env_821_,
                    v_a_816_,
                    v_asyncMode_837_,
                    v___x_838_,
                );
                if v_isShared_834_ == 0 {
                    leanh::lean_ctor_set(v___x_833_, 0, v___x_839_);
                    v___x_841_ = v___x_833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_847_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 1, v_messages_822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 2, v_scopes_823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 3, v_usedQuotCtxts_824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 4, v_nextMacroScope_825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 5, v_maxRecDepth_826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 6, v_ngen_827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 7, v_auxDeclNGen_828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 8, v_infoState_829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 9, v_traceState_830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_847_, 10, v_snapshotTasks_831_);
                    v___x_841_ = v_reuseFailAlloc_847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_842_ = lean_st_ref_set(v_a_799_, v___x_841_);
                v___x_843_ = leanh::lean_box(0);
                if v_isShared_819_ == 0 {
                    leanh::lean_ctor_set(v___x_818_, 0, v___x_843_);
                    v___x_845_ = v___x_818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
                    v___x_845_ = v_reuseFailAlloc_846_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___boxed(
    mut v_stx_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ =
        l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated(
            v_stx_850_, v_a_851_, v_a_852_,
        );
    leanh::lean_dec(v_a_852_);
    leanh::lean_dec_ref(v_a_851_);
    return v_res_854_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1(
    mut v_msgData_855_: *mut leanh::LeanObject,
    mut v___y_856_: *mut leanh::LeanObject,
    mut v___y_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(v_msgData_855_, v___y_857_);
    return v___x_859_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___boxed(
    mut v_msgData_860_: *mut leanh::LeanObject,
    mut v___y_861_: *mut leanh::LeanObject,
    mut v___y_862_: *mut leanh::LeanObject,
    mut v___y_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1(v_msgData_860_, v___y_861_, v___y_862_);
    leanh::lean_dec(v___y_862_);
    leanh::lean_dec_ref(v___y_861_);
    return v_res_864_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1(
    mut v_00_u03b1_865_: *mut leanh::LeanObject,
    mut v_msg_866_: *mut leanh::LeanObject,
    mut v___y_867_: *mut leanh::LeanObject,
    mut v___y_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(v_msg_866_, v___y_867_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___boxed(
    mut v_00_u03b1_871_: *mut leanh::LeanObject,
    mut v_msg_872_: *mut leanh::LeanObject,
    mut v___y_873_: *mut leanh::LeanObject,
    mut v___y_874_: *mut leanh::LeanObject,
    mut v___y_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_876_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1(v_00_u03b1_871_, v_msg_872_, v___y_873_, v___y_874_);
    leanh::lean_dec(v___y_874_);
    leanh::lean_dec_ref(v___y_873_);
    return v_res_876_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2(
    mut v_msgData_877_: *mut leanh::LeanObject,
    mut v_macroStack_878_: *mut leanh::LeanObject,
    mut v___y_879_: *mut leanh::LeanObject,
    mut v___y_880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(v_msgData_877_, v_macroStack_878_, v___y_880_);
    return v___x_882_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___boxed(
    mut v_msgData_883_: *mut leanh::LeanObject,
    mut v_macroStack_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
    mut v___y_886_: *mut leanh::LeanObject,
    mut v___y_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2(v_msgData_883_, v_macroStack_884_, v___y_885_, v___y_886_);
    leanh::lean_dec(v___y_886_);
    leanh::lean_dec_ref(v___y_885_);
    return v_res_888_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1()
-> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_895_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3;
    v___x_896_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1;
    v___x_897_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_898_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_894_, v___x_895_, v___x_896_, v___x_897_,
    );
    return v___x_898_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___boxed(
    mut v_a_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1();
    return v_res_900_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Annotated(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt,
    );
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Annotated(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Annotated(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
}