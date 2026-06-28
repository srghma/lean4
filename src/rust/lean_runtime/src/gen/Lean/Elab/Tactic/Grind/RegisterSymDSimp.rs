// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.RegisterSymDSimp
// Imports: Init.Sym.DSimp.DSimprocDSL Lean.Meta.Sym.DSimp.Variant Lean.Elab.Tactic.Grind.DSimprocDSL Lean.Elab.Tactic.Grind.WithGrindTacticM
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getNat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Sym::DSimp::DSimprocDSL::{
    initialize_Init_Sym_DSimp_DSimprocDSL, runtime_initialize_Init_Sym_DSimp_DSimprocDSL,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_getRef___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::DSimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_DSimprocDSL,
    l_Lean_Elab_Tactic_Grind_elabSymDSimproc___boxed,
    runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::WithGrindTacticM::{
    initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM,
    l_Lean_Elab_Command_withGrindTacticM___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Variant::{
    initialize_Lean_Meta_Sym_DSimp_Variant, l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f,
    l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension, runtime_initialize_Lean_Meta_Sym_DSimp_Variant,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_addEntry___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__3_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 83, 116, 101, 112, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,9043302130081388410 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__5_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 114, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,1566494510409085648 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__7_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 111, 115, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,7104639290947524305 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__9_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__11_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 112, 111, 115, 116, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__13_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 112, 114, 101, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__15_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 109, 97, 120, 83, 116, 101, 112, 115, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__17_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__17_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [83, 121, 109, 46, 100, 115, 105, 109, 112, 32, 118, 97, 114, 105, 97, 110, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__4_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__0_value) as *mut crate::leanh::LeanObject,11904518328331150023 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__2_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__5_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__7_value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__9_value) as *mut crate::leanh::LeanObject,4907018543776028915 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__11_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__11_value) as *mut crate::leanh::LeanObject,17726852515246642857 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3129047761607404012 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,3479794513963093741 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__5_value) as *mut crate::leanh::LeanObject,7434730390598631803 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,7168569217608292234 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__17_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 108, 97, 98, 82, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__16_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__17_value) as *mut crate::leanh::LeanObject,7969182454730956935 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_validateOptionDSimprocSyntax(
    mut v_proc_x3f_591_: *mut crate::leanh::LeanObject,
    mut v_a_592_: *mut crate::leanh::LeanObject,
    mut v_a_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_proc_x3f_591_) == 1 {
                    v_val_595_ = crate::leanh::lean_ctor_get(v_proc_x3f_591_, 0);
                    crate::leanh::lean_inc(v_val_595_);
                    crate::leanh::lean_dec_ref_known(v_proc_x3f_591_, 1);
                    v___x_596_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Grind_elabSymDSimproc___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_596_, 0, v_val_595_);
                    v___x_597_ = l_Lean_Elab_Command_withGrindTacticM___redArg(
                        v___x_596_, v_a_592_, v_a_593_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_597_) == 0 {
                        v_isSharedCheck_605_ = (!crate::leanh::lean_is_exclusive(v___x_597_)) as u8;
                        if v_isSharedCheck_605_ == 0 {
                            v_unused_606_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                            crate::leanh::lean_dec(v_unused_606_);
                            v___x_599_ = v___x_597_;
                            v_isShared_600_ = v_isSharedCheck_605_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_597_);
                            v___x_599_ = crate::leanh::lean_box(0);
                            v_isShared_600_ = v_isSharedCheck_605_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_607_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                        v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v___x_597_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v___x_609_ = v___x_597_;
                            v_isShared_610_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_607_);
                            crate::leanh::lean_dec(v___x_597_);
                            v___x_609_ = crate::leanh::lean_box(0);
                            v_isShared_610_ = v_isSharedCheck_614_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_proc_x3f_591_);
                    v___x_615_ = crate::leanh::lean_box(0);
                    v___x_616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_616_, 0, v___x_615_);
                    return v___x_616_;
                }
            }
            1 => {
                v___x_601_ = crate::leanh::lean_box(0);
                if v_isShared_600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_599_, 0, v___x_601_);
                    v___x_603_ = v___x_599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
                    v___x_603_ = v_reuseFailAlloc_604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_603_;
            }
            3 => {
                if v_isShared_610_ == 0 {
                    v___x_612_ = v___x_609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_validateOptionDSimprocSyntax___boxed(
    mut v_proc_x3f_617_: *mut crate::leanh::LeanObject,
    mut v_a_618_: *mut crate::leanh::LeanObject,
    mut v_a_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_validateOptionDSimprocSyntax(v_proc_x3f_617_, v_a_618_, v_a_619_);
    crate::leanh::lean_dec(v_a_619_);
    crate::leanh::lean_dec_ref(v_a_618_);
    return v_res_621_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = crate::leanh::lean_box(1);
    v___x_623_ = l_Lean_MessageData_ofFormat(v___x_622_);
    return v___x_623_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__2;
    v___x_628_ = l_Lean_MessageData_ofFormat(v___x_627_);
    return v___x_628_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5(
    mut v_x_629_: *mut crate::leanh::LeanObject,
    mut v_x_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v_before_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_652_: u8 = 0;
    let mut v_unused_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_630_) == 0 {
                    return v_x_629_;
                } else {
                    v_head_631_ = crate::leanh::lean_ctor_get(v_x_630_, 0);
                    v_tail_632_ = crate::leanh::lean_ctor_get(v_x_630_, 1);
                    v_isSharedCheck_654_ = (!crate::leanh::lean_is_exclusive(v_x_630_)) as u8;
                    if v_isSharedCheck_654_ == 0 {
                        v___x_634_ = v_x_630_;
                        v_isShared_635_ = v_isSharedCheck_654_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_632_);
                        crate::leanh::lean_inc(v_head_631_);
                        crate::leanh::lean_dec(v_x_630_);
                        v___x_634_ = crate::leanh::lean_box(0);
                        v_isShared_635_ = v_isSharedCheck_654_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_636_ = crate::leanh::lean_ctor_get(v_head_631_, 0);
                v_isSharedCheck_652_ = (!crate::leanh::lean_is_exclusive(v_head_631_)) as u8;
                if v_isSharedCheck_652_ == 0 {
                    v_unused_653_ = crate::leanh::lean_ctor_get(v_head_631_, 1);
                    crate::leanh::lean_dec(v_unused_653_);
                    v___x_638_ = v_head_631_;
                    v_isShared_639_ = v_isSharedCheck_652_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_636_);
                    crate::leanh::lean_dec(v_head_631_);
                    v___x_638_ = crate::leanh::lean_box(0);
                    v_isShared_639_ = v_isSharedCheck_652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_639_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_638_, 7);
                    crate::leanh::lean_ctor_set(v___x_638_, 1, v___x_640_);
                    crate::leanh::lean_ctor_set(v___x_638_, 0, v_x_629_);
                    v___x_642_ = v___x_638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_651_, 0, v_x_629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_640_);
                    v___x_642_ = v_reuseFailAlloc_651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_643_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__3);
                if v_isShared_635_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_634_, 7);
                    crate::leanh::lean_ctor_set(v___x_634_, 1, v___x_643_);
                    crate::leanh::lean_ctor_set(v___x_634_, 0, v___x_642_);
                    v___x_645_ = v___x_634_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_650_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_643_);
                    v___x_645_ = v_reuseFailAlloc_650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_646_ = l_Lean_MessageData_ofSyntax(v_before_636_);
                v___x_647_ = l_Lean_indentD(v___x_646_);
                v___x_648_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_648_, 0, v___x_645_);
                crate::leanh::lean_ctor_set(v___x_648_, 1, v___x_647_);
                v_x_629_ = v___x_648_;
                v_x_630_ = v_tail_632_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__4(
    mut v_opts_655_: *mut crate::leanh::LeanObject,
    mut v_opt_656_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_657_ = crate::leanh::lean_ctor_get(v_opt_656_, 0);
    v_defValue_658_ = crate::leanh::lean_ctor_get(v_opt_656_, 1);
    v_map_659_ = crate::leanh::lean_ctor_get(v_opts_655_, 0);
    v___x_660_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_659_,
            v_name_657_,
        );
    if crate::leanh::lean_obj_tag(v___x_660_) == 0 {
        let mut v___x_661_: u8 = 0;
        v___x_661_ = (crate::leanh::lean_unbox(v_defValue_658_) as u8);
        return v___x_661_;
    } else {
        let mut v_val_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_662_ = crate::leanh::lean_ctor_get(v___x_660_, 0);
        crate::leanh::lean_inc(v_val_662_);
        crate::leanh::lean_dec_ref_known(v___x_660_, 1);
        if crate::leanh::lean_obj_tag(v_val_662_) == 1 {
            let mut v_v_663_: u8 = 0;
            v_v_663_ = crate::leanh::lean_ctor_get_uint8(v_val_662_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_662_, 0);
            return v_v_663_;
        } else {
            let mut v___x_664_: u8 = 0;
            crate::leanh::lean_dec(v_val_662_);
            v___x_664_ = (crate::leanh::lean_unbox(v_defValue_658_) as u8);
            return v___x_664_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_opts_665_: *mut crate::leanh::LeanObject,
    mut v_opt_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_667_: u8 = 0;
    let mut v_r_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__4(v_opts_665_, v_opt_666_);
    crate::leanh::lean_dec_ref(v_opt_666_);
    crate::leanh::lean_dec_ref(v_opts_665_);
    v_r_668_ = crate::leanh::lean_box((v_res_667_) as usize);
    return v_r_668_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_673_ = l_Lean_MessageData_ofFormat(v___x_672_);
    return v___x_673_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_674_: *mut crate::leanh::LeanObject,
    mut v_macroStack_675_: *mut crate::leanh::LeanObject,
    mut v___y_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut v_unused_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_678_ = lean_st_ref_get(v___y_676_);
                v_scopes_679_ = crate::leanh::lean_ctor_get(v___x_678_, 2);
                crate::leanh::lean_inc(v_scopes_679_);
                crate::leanh::lean_dec(v___x_678_);
                v___x_680_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_681_ = l_List_head_x21___redArg(v___x_680_, v_scopes_679_);
                crate::leanh::lean_dec(v_scopes_679_);
                v_opts_682_ = crate::leanh::lean_ctor_get(v___x_681_, 1);
                crate::leanh::lean_inc_ref(v_opts_682_);
                crate::leanh::lean_dec(v___x_681_);
                v___x_683_ = l_Lean_Elab_pp_macroStack;
                v___x_684_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__4(v_opts_682_, v___x_683_);
                crate::leanh::lean_dec_ref(v_opts_682_);
                if v___x_684_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_675_);
                    v___x_685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_685_, 0, v_msgData_674_);
                    return v___x_685_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_675_) == 0 {
                        v___x_686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_686_, 0, v_msgData_674_);
                        return v___x_686_;
                    } else {
                        v_head_687_ = crate::leanh::lean_ctor_get(v_macroStack_675_, 0);
                        crate::leanh::lean_inc(v_head_687_);
                        v_after_688_ = crate::leanh::lean_ctor_get(v_head_687_, 1);
                        v_isSharedCheck_703_ =
                            (!crate::leanh::lean_is_exclusive(v_head_687_)) as u8;
                        if v_isSharedCheck_703_ == 0 {
                            v_unused_704_ = crate::leanh::lean_ctor_get(v_head_687_, 0);
                            crate::leanh::lean_dec(v_unused_704_);
                            v___x_690_ = v_head_687_;
                            v_isShared_691_ = v_isSharedCheck_703_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_688_);
                            crate::leanh::lean_dec(v_head_687_);
                            v___x_690_ = crate::leanh::lean_box(0);
                            v_isShared_691_ = v_isSharedCheck_703_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_691_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_690_, 7);
                    crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_692_);
                    crate::leanh::lean_ctor_set(v___x_690_, 0, v_msgData_674_);
                    v___x_694_ = v___x_690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_702_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_702_, 0, v_msgData_674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_692_);
                    v___x_694_ = v_reuseFailAlloc_702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_695_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_696_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_696_, 0, v___x_694_);
                crate::leanh::lean_ctor_set(v___x_696_, 1, v___x_695_);
                v___x_697_ = l_Lean_MessageData_ofSyntax(v_after_688_);
                v___x_698_ = l_Lean_indentD(v___x_697_);
                v_msgData_699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_699_, 0, v___x_696_);
                crate::leanh::lean_ctor_set(v_msgData_699_, 1, v___x_698_);
                v___x_700_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2_spec__5(v_msgData_699_, v_macroStack_675_);
                v___x_701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_701_, 0, v___x_700_);
                return v___x_701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_705_: *mut crate::leanh::LeanObject,
    mut v_macroStack_706_: *mut crate::leanh::LeanObject,
    mut v___y_707_: *mut crate::leanh::LeanObject,
    mut v___y_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg(v_msgData_705_, v_macroStack_706_, v___y_707_);
    crate::leanh::lean_dec(v___y_707_);
    return v_res_709_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_710_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_711_);
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_714_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_715_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_714_);
    crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
    crate::leanh::lean_ctor_set(v___x_715_, 2, v___x_714_);
    crate::leanh::lean_ctor_set(v___x_715_, 3, v___x_714_);
    crate::leanh::lean_ctor_set(v___x_715_, 4, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 5, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 6, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 7, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 8, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_715_, 9, v___x_713_);
    return v___x_715_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_717_ = lean_mk_empty_array_with_capacity(v___x_716_);
    v___x_718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_718_, 0, v___x_717_);
    return v___x_718_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_719_: usize = 0;
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = 5usize;
    v___x_720_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_721_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_722_ = lean_mk_empty_array_with_capacity(v___x_721_);
    v___x_723_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_724_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_724_, 0, v___x_723_);
    crate::leanh::lean_ctor_set(v___x_724_, 1, v___x_722_);
    crate::leanh::lean_ctor_set(v___x_724_, 2, v___x_720_);
    crate::leanh::lean_ctor_set(v___x_724_, 3, v___x_720_);
    crate::leanh::lean_ctor_set_usize(v___x_724_, 4, v___x_719_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = crate::leanh::lean_box(1);
    v___x_726_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_727_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_728_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_727_);
    crate::leanh::lean_ctor_set(v___x_728_, 1, v___x_726_);
    crate::leanh::lean_ctor_set(v___x_728_, 2, v___x_725_);
    return v___x_728_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = lean_st_ref_get(v___y_730_);
    v_env_733_ = crate::leanh::lean_ctor_get(v___x_732_, 0);
    crate::leanh::lean_inc_ref(v_env_733_);
    crate::leanh::lean_dec(v___x_732_);
    v___x_734_ = lean_st_ref_get(v___y_730_);
    v_scopes_735_ = crate::leanh::lean_ctor_get(v___x_734_, 2);
    crate::leanh::lean_inc(v_scopes_735_);
    crate::leanh::lean_dec(v___x_734_);
    v___x_736_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_737_ = l_List_head_x21___redArg(v___x_736_, v_scopes_735_);
    crate::leanh::lean_dec(v_scopes_735_);
    v_opts_738_ = crate::leanh::lean_ctor_get(v___x_737_, 1);
    crate::leanh::lean_inc_ref(v_opts_738_);
    crate::leanh::lean_dec(v___x_737_);
    v___x_739_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__2);
    v___x_740_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___closed__5);
    v___x_741_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_741_, 0, v_env_733_);
    crate::leanh::lean_ctor_set(v___x_741_, 1, v___x_739_);
    crate::leanh::lean_ctor_set(v___x_741_, 2, v___x_740_);
    crate::leanh::lean_ctor_set(v___x_741_, 3, v_opts_738_);
    v___x_742_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_742_, 0, v___x_741_);
    crate::leanh::lean_ctor_set(v___x_742_, 1, v_msgData_729_);
    v___x_743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_743_, 0, v___x_742_);
    return v___x_743_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_747_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg(v_msgData_744_, v___y_745_);
    crate::leanh::lean_dec(v___y_745_);
    return v_res_747_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___redArg(
    mut v_msg_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_a_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_771_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_752_ = l_Lean_Elab_Command_getRef___redArg(v___y_749_);
                if crate::leanh::lean_obj_tag(v___x_752_) == 0 {
                    v_a_753_ = crate::leanh::lean_ctor_get(v___x_752_, 0);
                    crate::leanh::lean_inc(v_a_753_);
                    crate::leanh::lean_dec_ref_known(v___x_752_, 1);
                    v_macroStack_754_ = crate::leanh::lean_ctor_get(v___y_749_, 4);
                    v___x_755_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg(v_msg_748_, v___y_750_);
                    v_a_756_ = crate::leanh::lean_ctor_get(v___x_755_, 0);
                    crate::leanh::lean_inc(v_a_756_);
                    crate::leanh::lean_dec_ref(v___x_755_);
                    v___x_757_ = l_Lean_Elab_getBetterRef(v_a_753_, v_macroStack_754_);
                    crate::leanh::lean_dec(v_a_753_);
                    crate::leanh::lean_inc(v_macroStack_754_);
                    v___x_758_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg(v_a_756_, v_macroStack_754_, v___y_750_);
                    v_a_759_ = crate::leanh::lean_ctor_get(v___x_758_, 0);
                    v_isSharedCheck_767_ = (!crate::leanh::lean_is_exclusive(v___x_758_)) as u8;
                    if v_isSharedCheck_767_ == 0 {
                        v___x_761_ = v___x_758_;
                        v_isShared_762_ = v_isSharedCheck_767_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_759_);
                        crate::leanh::lean_dec(v___x_758_);
                        v___x_761_ = crate::leanh::lean_box(0);
                        v_isShared_762_ = v_isSharedCheck_767_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_748_);
                    v_a_768_ = crate::leanh::lean_ctor_get(v___x_752_, 0);
                    v_isSharedCheck_775_ = (!crate::leanh::lean_is_exclusive(v___x_752_)) as u8;
                    if v_isSharedCheck_775_ == 0 {
                        v___x_770_ = v___x_752_;
                        v_isShared_771_ = v_isSharedCheck_775_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_768_);
                        crate::leanh::lean_dec(v___x_752_);
                        v___x_770_ = crate::leanh::lean_box(0);
                        v_isShared_771_ = v_isSharedCheck_775_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_763_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_763_, 0, v___x_757_);
                crate::leanh::lean_ctor_set(v___x_763_, 1, v_a_759_);
                if v_isShared_762_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_761_, 1);
                    crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_763_);
                    v___x_765_ = v___x_761_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
                    v___x_765_ = v_reuseFailAlloc_766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_765_;
            }
            3 => {
                if v_isShared_771_ == 0 {
                    v___x_773_ = v___x_770_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
                    v___x_773_ = v_reuseFailAlloc_774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___redArg___boxed(
    mut v_msg_776_: *mut crate::leanh::LeanObject,
    mut v___y_777_: *mut crate::leanh::LeanObject,
    mut v___y_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___redArg(v_msg_776_, v___y_777_, v___y_778_);
    crate::leanh::lean_dec(v___y_778_);
    crate::leanh::lean_dec_ref(v___y_777_);
    return v_res_780_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(
    mut v_ref_781_: *mut crate::leanh::LeanObject,
    mut v_msg_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_797_: u8 = 0;
    let mut v_ref_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_786_ = l_Lean_Elab_Command_getRef___redArg(v___y_783_);
                if crate::leanh::lean_obj_tag(v___x_786_) == 0 {
                    v_a_787_ = crate::leanh::lean_ctor_get(v___x_786_, 0);
                    crate::leanh::lean_inc(v_a_787_);
                    crate::leanh::lean_dec_ref_known(v___x_786_, 1);
                    v_fileName_788_ = crate::leanh::lean_ctor_get(v___y_783_, 0);
                    v_fileMap_789_ = crate::leanh::lean_ctor_get(v___y_783_, 1);
                    v_currRecDepth_790_ = crate::leanh::lean_ctor_get(v___y_783_, 2);
                    v_cmdPos_791_ = crate::leanh::lean_ctor_get(v___y_783_, 3);
                    v_macroStack_792_ = crate::leanh::lean_ctor_get(v___y_783_, 4);
                    v_quotContext_x3f_793_ = crate::leanh::lean_ctor_get(v___y_783_, 5);
                    v_currMacroScope_794_ = crate::leanh::lean_ctor_get(v___y_783_, 6);
                    v_snap_x3f_795_ = crate::leanh::lean_ctor_get(v___y_783_, 8);
                    v_cancelTk_x3f_796_ = crate::leanh::lean_ctor_get(v___y_783_, 9);
                    v_suppressElabErrors_797_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_783_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_798_ = l_Lean_replaceRef(v_ref_781_, v_a_787_);
                    crate::leanh::lean_dec(v_a_787_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_796_);
                    crate::leanh::lean_inc(v_snap_x3f_795_);
                    crate::leanh::lean_inc(v_currMacroScope_794_);
                    crate::leanh::lean_inc(v_quotContext_x3f_793_);
                    crate::leanh::lean_inc(v_macroStack_792_);
                    crate::leanh::lean_inc(v_cmdPos_791_);
                    crate::leanh::lean_inc(v_currRecDepth_790_);
                    crate::leanh::lean_inc_ref(v_fileMap_789_);
                    crate::leanh::lean_inc_ref(v_fileName_788_);
                    v___x_799_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_799_, 0, v_fileName_788_);
                    crate::leanh::lean_ctor_set(v___x_799_, 1, v_fileMap_789_);
                    crate::leanh::lean_ctor_set(v___x_799_, 2, v_currRecDepth_790_);
                    crate::leanh::lean_ctor_set(v___x_799_, 3, v_cmdPos_791_);
                    crate::leanh::lean_ctor_set(v___x_799_, 4, v_macroStack_792_);
                    crate::leanh::lean_ctor_set(v___x_799_, 5, v_quotContext_x3f_793_);
                    crate::leanh::lean_ctor_set(v___x_799_, 6, v_currMacroScope_794_);
                    crate::leanh::lean_ctor_set(v___x_799_, 7, v_ref_798_);
                    crate::leanh::lean_ctor_set(v___x_799_, 8, v_snap_x3f_795_);
                    crate::leanh::lean_ctor_set(v___x_799_, 9, v_cancelTk_x3f_796_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_799_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_797_,
                    );
                    v___x_800_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___redArg(v_msg_782_, v___x_799_, v___y_784_);
                    crate::leanh::lean_dec_ref_known(v___x_799_, 10);
                    return v___x_800_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_782_);
                    v_a_801_ = crate::leanh::lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_808_ = (!crate::leanh::lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_808_ == 0 {
                        v___x_803_ = v___x_786_;
                        v_isShared_804_ = v_isSharedCheck_808_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_801_);
                        crate::leanh::lean_dec(v___x_786_);
                        v___x_803_ = crate::leanh::lean_box(0);
                        v_isShared_804_ = v_isSharedCheck_808_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_804_ == 0 {
                    v___x_806_ = v___x_803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
                    v___x_806_ = v_reuseFailAlloc_807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg___boxed(
    mut v_ref_809_: *mut crate::leanh::LeanObject,
    mut v_msg_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_ref_809_, v_msg_810_, v___y_811_, v___y_812_);
    crate::leanh::lean_dec(v___y_812_);
    crate::leanh::lean_dec_ref(v___y_811_);
    crate::leanh::lean_dec(v_ref_809_);
    return v_res_814_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__9;
    v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
    return v___x_838_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__11;
    v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
    return v___x_841_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__13;
    v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
    return v___x_844_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__15;
    v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
    return v___x_847_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1(
    mut v_as_851_: *mut crate::leanh::LeanObject,
    mut v_sz_852_: usize,
    mut v_i_853_: usize,
    mut v_b_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: usize = 0;
    let mut v___x_861_: usize = 0;
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v_fst_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v_a_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_909_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_931_: u8 = 0;
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: u8 = 0;
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_973_: u8 = 0;
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut v_isSharedCheck_978_: u8 = 0;
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_863_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
                if v___x_863_ == 0 {
                    v___x_864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_864_, 0, v_b_854_);
                    return v___x_864_;
                } else {
                    v_snd_865_ = crate::leanh::lean_ctor_get(v_b_854_, 1);
                    v_fst_866_ = crate::leanh::lean_ctor_get(v_b_854_, 0);
                    v_isSharedCheck_979_ = (!crate::leanh::lean_is_exclusive(v_b_854_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v___x_868_ = v_b_854_;
                        v_isShared_869_ = v_isSharedCheck_979_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_865_);
                        crate::leanh::lean_inc(v_fst_866_);
                        crate::leanh::lean_dec(v_b_854_);
                        v___x_868_ = crate::leanh::lean_box(0);
                        v_isShared_869_ = v_isSharedCheck_979_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_860_ = 1usize;
                v___x_861_ = lean_usize_add(v_i_853_, v___x_860_);
                v_i_853_ = v___x_861_;
                v_b_854_ = v_a_859_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_870_ = crate::leanh::lean_ctor_get(v_snd_865_, 0);
                v_snd_871_ = crate::leanh::lean_ctor_get(v_snd_865_, 1);
                v_isSharedCheck_978_ = (!crate::leanh::lean_is_exclusive(v_snd_865_)) as u8;
                if v_isSharedCheck_978_ == 0 {
                    v___x_873_ = v_snd_865_;
                    v_isShared_874_ = v_isSharedCheck_978_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_871_);
                    crate::leanh::lean_inc(v_fst_870_);
                    crate::leanh::lean_dec(v_snd_865_);
                    v___x_873_ = crate::leanh::lean_box(0);
                    v_isShared_874_ = v_isSharedCheck_978_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_875_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
                v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__4;
                crate::leanh::lean_inc(v_a_875_);
                v___x_877_ = l_Lean_Syntax_isOfKind(v_a_875_, v___x_876_);
                if v___x_877_ == 0 {
                    v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__6;
                    crate::leanh::lean_inc(v_a_875_);
                    v___x_879_ = l_Lean_Syntax_isOfKind(v_a_875_, v___x_878_);
                    if v___x_879_ == 0 {
                        v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__8;
                        crate::leanh::lean_inc(v_a_875_);
                        v___x_881_ = l_Lean_Syntax_isOfKind(v_a_875_, v___x_880_);
                        if v___x_881_ == 0 {
                            v___x_882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10);
                            v___x_883_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_a_875_, v___x_882_, v___y_855_, v___y_856_);
                            if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_883_, 1);
                                if v_isShared_874_ == 0 {
                                    v___x_885_ = v___x_873_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_889_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_889_,
                                        0,
                                        v_fst_870_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_889_,
                                        1,
                                        v_snd_871_,
                                    );
                                    v___x_885_ = v_reuseFailAlloc_889_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_873_);
                                crate::leanh::lean_dec(v_snd_871_);
                                crate::leanh::lean_dec(v_fst_870_);
                                crate::leanh::lean_del_object(v___x_868_);
                                crate::leanh::lean_dec(v_fst_866_);
                                v_a_890_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                                v_isSharedCheck_897_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                                if v_isSharedCheck_897_ == 0 {
                                    v___x_892_ = v___x_883_;
                                    v_isShared_893_ = v_isSharedCheck_897_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_890_);
                                    crate::leanh::lean_dec(v___x_883_);
                                    v___x_892_ = crate::leanh::lean_box(0);
                                    v_isShared_893_ = v_isSharedCheck_897_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            v___x_898_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_899_ = l_Lean_Syntax_getArg(v_a_875_, v___x_898_);
                            if crate::leanh::lean_obj_tag(v_fst_870_) == 0 {
                                v___y_909_ = v___x_881_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_fst_870_, 1);
                                v___y_909_ = v___x_879_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_920_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_921_ = l_Lean_Syntax_getArg(v_a_875_, v___x_920_);
                        if crate::leanh::lean_obj_tag(v_fst_866_) == 0 {
                            v___y_931_ = v___x_879_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fst_866_, 1);
                            v___y_931_ = v___x_877_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v___x_942_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_943_ = l_Lean_Syntax_getArg(v_a_875_, v___x_942_);
                    v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__18;
                    crate::leanh::lean_inc(v___x_943_);
                    v___x_965_ = l_Lean_Syntax_isOfKind(v___x_943_, v___x_964_);
                    if v___x_965_ == 0 {
                        crate::leanh::lean_dec(v___x_943_);
                        crate::leanh::lean_del_object(v___x_873_);
                        crate::leanh::lean_del_object(v___x_868_);
                        v___x_966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__10);
                        v___x_967_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_a_875_, v___x_966_, v___y_855_, v___y_856_);
                        if crate::leanh::lean_obj_tag(v___x_967_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_967_, 1);
                            v___x_968_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_968_, 0, v_fst_870_);
                            crate::leanh::lean_ctor_set(v___x_968_, 1, v_snd_871_);
                            v___x_969_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_969_, 0, v_fst_866_);
                            crate::leanh::lean_ctor_set(v___x_969_, 1, v___x_968_);
                            v_a_859_ = v___x_969_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_871_);
                            crate::leanh::lean_dec(v_fst_870_);
                            crate::leanh::lean_dec(v_fst_866_);
                            v_a_970_ = crate::leanh::lean_ctor_get(v___x_967_, 0);
                            v_isSharedCheck_977_ =
                                (!crate::leanh::lean_is_exclusive(v___x_967_)) as u8;
                            if v_isSharedCheck_977_ == 0 {
                                v___x_972_ = v___x_967_;
                                v_isShared_973_ = v_isSharedCheck_977_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_970_);
                                crate::leanh::lean_dec(v___x_967_);
                                v___x_972_ = crate::leanh::lean_box(0);
                                v_isShared_973_ = v_isSharedCheck_977_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_snd_871_) == 0 {
                            if v___x_965_ == 0 {
                                state = 23;
                                continue;
                            } else {
                                state = 20;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_snd_871_, 1);
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_885_);
                    v___x_887_ = v___x_868_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
                    v___x_887_ = v_reuseFailAlloc_888_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_859_ = v___x_887_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_895_;
            }
            8 => {
                v___x_901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_899_);
                if v_isShared_874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_901_);
                    v___x_903_ = v___x_873_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_871_);
                    v___x_903_ = v_reuseFailAlloc_907_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_903_);
                    v___x_905_ = v___x_868_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
                    v___x_905_ = v_reuseFailAlloc_906_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_859_ = v___x_905_;
                state = 1;
                continue;
            }
            11 => {
                if v___y_909_ == 0 {
                    v___x_910_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__12);
                    v___x_911_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_a_875_, v___x_910_, v___y_855_, v___y_856_);
                    if crate::leanh::lean_obj_tag(v___x_911_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_911_, 1);
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_899_);
                        crate::leanh::lean_del_object(v___x_873_);
                        crate::leanh::lean_dec(v_snd_871_);
                        crate::leanh::lean_del_object(v___x_868_);
                        crate::leanh::lean_dec(v_fst_866_);
                        v_a_912_ = crate::leanh::lean_ctor_get(v___x_911_, 0);
                        v_isSharedCheck_919_ = (!crate::leanh::lean_is_exclusive(v___x_911_)) as u8;
                        if v_isSharedCheck_919_ == 0 {
                            v___x_914_ = v___x_911_;
                            v_isShared_915_ = v_isSharedCheck_919_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_912_);
                            crate::leanh::lean_dec(v___x_911_);
                            v___x_914_ = crate::leanh::lean_box(0);
                            v_isShared_915_ = v_isSharedCheck_919_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            12 => {
                if v_isShared_915_ == 0 {
                    v___x_917_ = v___x_914_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
                    v___x_917_ = v_reuseFailAlloc_918_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_917_;
            }
            14 => {
                v___x_923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
                if v_isShared_874_ == 0 {
                    v___x_925_ = v___x_873_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v_fst_870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 1, v_snd_871_);
                    v___x_925_ = v_reuseFailAlloc_929_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_925_);
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_923_);
                    v___x_927_ = v___x_868_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_925_);
                    v___x_927_ = v_reuseFailAlloc_928_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_a_859_ = v___x_927_;
                state = 1;
                continue;
            }
            17 => {
                if v___y_931_ == 0 {
                    v___x_932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__14);
                    v___x_933_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_a_875_, v___x_932_, v___y_855_, v___y_856_);
                    if crate::leanh::lean_obj_tag(v___x_933_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_933_, 1);
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_921_);
                        crate::leanh::lean_del_object(v___x_873_);
                        crate::leanh::lean_dec(v_snd_871_);
                        crate::leanh::lean_dec(v_fst_870_);
                        crate::leanh::lean_del_object(v___x_868_);
                        v_a_934_ = crate::leanh::lean_ctor_get(v___x_933_, 0);
                        v_isSharedCheck_941_ = (!crate::leanh::lean_is_exclusive(v___x_933_)) as u8;
                        if v_isSharedCheck_941_ == 0 {
                            v___x_936_ = v___x_933_;
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_934_);
                            crate::leanh::lean_dec(v___x_933_);
                            v___x_936_ = crate::leanh::lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v_isShared_937_ == 0 {
                    v___x_939_ = v___x_936_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_939_;
            }
            20 => {
                v___x_945_ = l_Lean_TSyntax_getNat(v___x_943_);
                crate::leanh::lean_dec(v___x_943_);
                v___x_946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_946_, 0, v___x_945_);
                if v_isShared_874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_946_);
                    v___x_948_ = v___x_873_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fst_870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_946_);
                    v___x_948_ = v_reuseFailAlloc_952_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_948_);
                    v___x_950_ = v___x_868_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_951_, 0, v_fst_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_a_859_ = v___x_950_;
                state = 1;
                continue;
            }
            23 => {
                v___x_954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___closed__16);
                v___x_955_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_a_875_, v___x_954_, v___y_855_, v___y_856_);
                if crate::leanh::lean_obj_tag(v___x_955_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_955_, 1);
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_943_);
                    crate::leanh::lean_del_object(v___x_873_);
                    crate::leanh::lean_dec(v_fst_870_);
                    crate::leanh::lean_del_object(v___x_868_);
                    crate::leanh::lean_dec(v_fst_866_);
                    v_a_956_ = crate::leanh::lean_ctor_get(v___x_955_, 0);
                    v_isSharedCheck_963_ = (!crate::leanh::lean_is_exclusive(v___x_955_)) as u8;
                    if v_isSharedCheck_963_ == 0 {
                        v___x_958_ = v___x_955_;
                        v_isShared_959_ = v_isSharedCheck_963_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_956_);
                        crate::leanh::lean_dec(v___x_955_);
                        v___x_958_ = crate::leanh::lean_box(0);
                        v_isShared_959_ = v_isSharedCheck_963_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_959_ == 0 {
                    v___x_961_ = v___x_958_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
                    v___x_961_ = v_reuseFailAlloc_962_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_961_;
            }
            26 => {
                if v_isShared_973_ == 0 {
                    v___x_975_ = v___x_972_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
                    v___x_975_ = v_reuseFailAlloc_976_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1___boxed(
    mut v_as_980_: *mut crate::leanh::LeanObject,
    mut v_sz_981_: *mut crate::leanh::LeanObject,
    mut v_i_982_: *mut crate::leanh::LeanObject,
    mut v_b_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_987_: usize = 0;
    let mut v_i_boxed_988_: usize = 0;
    let mut v_res_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_987_ = crate::leanh::lean_unbox_usize(v_sz_981_);
    crate::leanh::lean_dec(v_sz_981_);
    v_i_boxed_988_ = crate::leanh::lean_unbox_usize(v_i_982_);
    crate::leanh::lean_dec(v_i_982_);
    v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1(v_as_980_, v_sz_boxed_987_, v_i_boxed_988_, v_b_983_, v___y_984_, v___y_985_);
    crate::leanh::lean_dec(v___y_985_);
    crate::leanh::lean_dec_ref(v___y_984_);
    crate::leanh::lean_dec_ref(v_as_980_);
    return v_res_989_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__2;
    v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
    return v___x_997_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__4;
    v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
    return v___x_1000_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp(
    mut v_stx_1001_: *mut crate::leanh::LeanObject,
    mut v_a_1002_: *mut crate::leanh::LeanObject,
    mut v_a_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v___y_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1005_ = lean_st_ref_get(v_a_1003_);
                v_env_1006_ = crate::leanh::lean_ctor_get(v___x_1005_, 0);
                crate::leanh::lean_inc_ref(v_env_1006_);
                crate::leanh::lean_dec(v___x_1005_);
                v___x_1007_ = crate::leanh::lean_unsigned_to_nat(1);
                v_id_1008_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1007_);
                v_name_1009_ = l_Lean_Syntax_getId(v_id_1008_);
                v___x_1068_ =
                    l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_1006_, v_name_1009_);
                if crate::leanh::lean_obj_tag(v___x_1068_) == 0 {
                    crate::leanh::lean_dec(v_id_1008_);
                    v___y_1042_ = v_a_1002_;
                    v___y_1043_ = v_a_1003_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1068_, 1);
                    v___x_1069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3_once), _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__3);
                    v___x_1070_ = l_Lean_MessageData_ofName(v_name_1009_);
                    v___x_1071_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1071_, 0, v___x_1069_);
                    crate::leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
                    v___x_1072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__5);
                    v___x_1073_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1071_);
                    crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1072_);
                    v___x_1074_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_id_1008_, v___x_1073_, v_a_1002_, v_a_1003_);
                    crate::leanh::lean_dec(v_id_1008_);
                    return v___x_1074_;
                }
            }
            1 => {
                v___x_1015_ = lean_st_ref_take(v___y_1011_);
                v_env_1016_ = crate::leanh::lean_ctor_get(v___x_1015_, 0);
                v_messages_1017_ = crate::leanh::lean_ctor_get(v___x_1015_, 1);
                v_scopes_1018_ = crate::leanh::lean_ctor_get(v___x_1015_, 2);
                v_usedQuotCtxts_1019_ = crate::leanh::lean_ctor_get(v___x_1015_, 3);
                v_nextMacroScope_1020_ = crate::leanh::lean_ctor_get(v___x_1015_, 4);
                v_maxRecDepth_1021_ = crate::leanh::lean_ctor_get(v___x_1015_, 5);
                v_ngen_1022_ = crate::leanh::lean_ctor_get(v___x_1015_, 6);
                v_auxDeclNGen_1023_ = crate::leanh::lean_ctor_get(v___x_1015_, 7);
                v_infoState_1024_ = crate::leanh::lean_ctor_get(v___x_1015_, 8);
                v_traceState_1025_ = crate::leanh::lean_ctor_get(v___x_1015_, 9);
                v_snapshotTasks_1026_ = crate::leanh::lean_ctor_get(v___x_1015_, 10);
                v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v___x_1015_)) as u8;
                if v_isSharedCheck_1040_ == 0 {
                    v___x_1028_ = v___x_1015_;
                    v_isShared_1029_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1026_);
                    crate::leanh::lean_inc(v_traceState_1025_);
                    crate::leanh::lean_inc(v_infoState_1024_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1023_);
                    crate::leanh::lean_inc(v_ngen_1022_);
                    crate::leanh::lean_inc(v_maxRecDepth_1021_);
                    crate::leanh::lean_inc(v_nextMacroScope_1020_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1019_);
                    crate::leanh::lean_inc(v_scopes_1018_);
                    crate::leanh::lean_inc(v_messages_1017_);
                    crate::leanh::lean_inc(v_env_1016_);
                    crate::leanh::lean_dec(v___x_1015_);
                    v___x_1028_ = crate::leanh::lean_box(0);
                    v_isShared_1029_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1030_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1030_, 0, v___y_1013_);
                crate::leanh::lean_ctor_set(v___x_1030_, 1, v___y_1012_);
                crate::leanh::lean_ctor_set(v___x_1030_, 2, v___y_1014_);
                v___x_1031_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
                v___x_1032_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1032_, 0, v_name_1009_);
                crate::leanh::lean_ctor_set(v___x_1032_, 1, v___x_1030_);
                v___x_1033_ = l_Lean_ScopedEnvExtension_addEntry___redArg(
                    v___x_1031_,
                    v_env_1016_,
                    v___x_1032_,
                );
                if v_isShared_1029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1028_, 0, v___x_1033_);
                    v___x_1035_ = v___x_1028_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_messages_1017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_scopes_1018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_usedQuotCtxts_1019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_nextMacroScope_1020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 5, v_maxRecDepth_1021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 6, v_ngen_1022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 7, v_auxDeclNGen_1023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 8, v_infoState_1024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 9, v_traceState_1025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 10, v_snapshotTasks_1026_);
                    v___x_1035_ = v_reuseFailAlloc_1039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1036_ = lean_st_ref_set(v___y_1011_, v___x_1035_);
                v___x_1037_ = crate::leanh::lean_box(0);
                v___x_1038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1037_);
                return v___x_1038_;
            }
            4 => {
                v___x_1044_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1045_ = l_Lean_Syntax_getArg(v_stx_1001_, v___x_1044_);
                v___x_1046_ = l_Lean_Syntax_getArgs(v___x_1045_);
                crate::leanh::lean_dec(v___x_1045_);
                v___x_1047_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___closed__1;
                v_sz_1048_ = lean_array_size(v___x_1046_);
                v___x_1049_ = 0usize;
                v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__1(v___x_1046_, v_sz_1048_, v___x_1049_, v___x_1047_, v___y_1042_, v___y_1043_);
                crate::leanh::lean_dec_ref(v___x_1046_);
                if crate::leanh::lean_obj_tag(v___x_1050_) == 0 {
                    v_a_1051_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                    crate::leanh::lean_inc(v_a_1051_);
                    crate::leanh::lean_dec_ref_known(v___x_1050_, 1);
                    v_fst_1052_ = crate::leanh::lean_ctor_get(v_a_1051_, 0);
                    crate::leanh::lean_inc_n(v_fst_1052_, 2);
                    v_snd_1053_ = crate::leanh::lean_ctor_get(v_a_1051_, 1);
                    crate::leanh::lean_inc(v_snd_1053_);
                    crate::leanh::lean_dec(v_a_1051_);
                    v___x_1054_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_validateOptionDSimprocSyntax(v_fst_1052_, v___y_1042_, v___y_1043_);
                    if crate::leanh::lean_obj_tag(v___x_1054_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1054_, 1);
                        v_fst_1055_ = crate::leanh::lean_ctor_get(v_snd_1053_, 0);
                        crate::leanh::lean_inc_n(v_fst_1055_, 2);
                        v_snd_1056_ = crate::leanh::lean_ctor_get(v_snd_1053_, 1);
                        crate::leanh::lean_inc(v_snd_1056_);
                        crate::leanh::lean_dec(v_snd_1053_);
                        v___x_1057_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_validateOptionDSimprocSyntax(v_fst_1055_, v___y_1042_, v___y_1043_);
                        if crate::leanh::lean_obj_tag(v___x_1057_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1057_, 1);
                            if crate::leanh::lean_obj_tag(v_snd_1056_) == 0 {
                                v___x_1058_ = crate::leanh::lean_unsigned_to_nat(100000);
                                v___y_1011_ = v___y_1043_;
                                v___y_1012_ = v_fst_1055_;
                                v___y_1013_ = v_fst_1052_;
                                v___y_1014_ = v___x_1058_;
                                state = 1;
                                continue;
                            } else {
                                v_val_1059_ = crate::leanh::lean_ctor_get(v_snd_1056_, 0);
                                crate::leanh::lean_inc(v_val_1059_);
                                crate::leanh::lean_dec_ref_known(v_snd_1056_, 1);
                                v___y_1011_ = v___y_1043_;
                                v___y_1012_ = v_fst_1055_;
                                v___y_1013_ = v_fst_1052_;
                                v___y_1014_ = v_val_1059_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_1056_);
                            crate::leanh::lean_dec(v_fst_1055_);
                            crate::leanh::lean_dec(v_fst_1052_);
                            crate::leanh::lean_dec(v_name_1009_);
                            return v___x_1057_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1053_);
                        crate::leanh::lean_dec(v_fst_1052_);
                        crate::leanh::lean_dec(v_name_1009_);
                        return v___x_1054_;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1009_);
                    v_a_1060_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                    v_isSharedCheck_1067_ = (!crate::leanh::lean_is_exclusive(v___x_1050_)) as u8;
                    if v_isSharedCheck_1067_ == 0 {
                        v___x_1062_ = v___x_1050_;
                        v_isShared_1063_ = v_isSharedCheck_1067_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1060_);
                        crate::leanh::lean_dec(v___x_1050_);
                        v___x_1062_ = crate::leanh::lean_box(0);
                        v_isShared_1063_ = v_isSharedCheck_1067_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1063_ == 0 {
                    v___x_1065_ = v___x_1062_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
                    v___x_1065_ = v_reuseFailAlloc_1066_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___boxed(
    mut v_stx_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1079_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp(v_stx_1075_, v_a_1076_, v_a_1077_);
    crate::leanh::lean_dec(v_a_1077_);
    crate::leanh::lean_dec_ref(v_a_1076_);
    crate::leanh::lean_dec(v_stx_1075_);
    return v_res_1079_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0(
    mut v_00_u03b1_1080_: *mut crate::leanh::LeanObject,
    mut v_ref_1081_: *mut crate::leanh::LeanObject,
    mut v_msg_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___redArg(v_ref_1081_, v_msg_1082_, v___y_1083_, v___y_1084_);
    return v___x_1086_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0___boxed(
    mut v_00_u03b1_1087_: *mut crate::leanh::LeanObject,
    mut v_ref_1088_: *mut crate::leanh::LeanObject,
    mut v_msg_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1093_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0(v_00_u03b1_1087_, v_ref_1088_, v_msg_1089_, v___y_1090_, v___y_1091_);
    crate::leanh::lean_dec(v___y_1091_);
    crate::leanh::lean_dec_ref(v___y_1090_);
    crate::leanh::lean_dec(v_ref_1088_);
    return v_res_1093_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1(
    mut v_msgData_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___redArg(v_msgData_1094_, v___y_1096_);
    return v___x_1098_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__1(v_msgData_1099_, v___y_1100_, v___y_1101_);
    crate::leanh::lean_dec(v___y_1101_);
    crate::leanh::lean_dec_ref(v___y_1100_);
    return v_res_1103_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0(
    mut v_00_u03b1_1104_: *mut crate::leanh::LeanObject,
    mut v_msg_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___redArg(v_msg_1105_, v___y_1106_, v___y_1107_);
    return v___x_1109_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0___boxed(
    mut v_00_u03b1_1110_: *mut crate::leanh::LeanObject,
    mut v_msg_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0(v_00_u03b1_1110_, v_msg_1111_, v___y_1112_, v___y_1113_);
    crate::leanh::lean_dec(v___y_1113_);
    crate::leanh::lean_dec_ref(v___y_1112_);
    return v_res_1115_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2(
    mut v_msgData_1116_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___redArg(v_msgData_1116_, v_macroStack_1117_, v___y_1119_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_1122_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp_spec__0_spec__0_spec__2(v_msgData_1122_, v_macroStack_1123_, v___y_1124_, v___y_1125_);
    crate::leanh::lean_dec(v___y_1125_);
    crate::leanh::lean_dec_ref(v___y_1124_);
    return v_res_1127_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1175_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__1;
    v___x_1176_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___closed__18;
    v___x_1177_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_1178_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1174_,
        v___x_1175_,
        v___x_1176_,
        v___x_1177_,
    );
    return v___x_1178_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1___boxed(
    mut v_a_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1();
    return v_res_1180_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymDSimp_0__Lean_Elab_Command_elabRegisterSymDSimp__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(builtin);
}
