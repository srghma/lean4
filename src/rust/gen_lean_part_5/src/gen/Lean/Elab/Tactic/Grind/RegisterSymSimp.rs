// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.RegisterSymSimp
// Imports: Init.Sym.Simp.SimprocDSL Lean.Meta.Sym.Simp.Variant Lean.Elab.Tactic.Grind.SimprocDSL Lean.Elab.Tactic.Grind.WithGrindTacticM
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getNat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Sym::Simp::SimprocDSL::{
    initialize_Init_Sym_Simp_SimprocDSL, runtime_initialize_Init_Sym_Simp_SimprocDSL,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_getRef___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::SimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_SimprocDSL, l_Lean_Elab_Tactic_Grind_elabSymSimproc___boxed,
    runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL,
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
use crate::r#gen::Lean::Meta::Sym::Simp::Variant::{
    initialize_Lean_Meta_Sym_Simp_Variant, l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f,
    l_Lean_Meta_Sym_Simp_symSimpVariantExtension, runtime_initialize_Lean_Meta_Sym_Simp_Variant,
};
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_addEntry___redArg;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__3_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 83, 116, 101, 112, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__3_value) as *mut leanh::LeanObject,1958772177027152643 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__5_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 68, 105, 115, 99, 104, 97, 114, 103, 101, 68, 101, 112, 116, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__5_value) as *mut leanh::LeanObject,6372041257667356148 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__7_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 114, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__7_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__7_value) as *mut leanh::LeanObject,9189406429225494327 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__9_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 111, 115, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__9_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__9_value) as *mut leanh::LeanObject,16195861106700361357 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__11_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__13_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 112, 111, 115, 116, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__15_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 112, 114, 101, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__17_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 109, 97, 120, 68, 105, 115, 99, 104, 97, 114, 103, 101, 68, 101, 112, 116, 104, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__19_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__19_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__21_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 96, 109, 97, 120, 83, 116, 101, 112, 115, 96, 32, 102, 105, 101, 108, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__21_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__3_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [83, 121, 109, 46, 115, 105, 109, 112, 32, 118, 97, 114, 105, 97, 110, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__5_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__0_value) as *mut leanh::LeanObject,258076495819451832 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__2_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__5_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__7_value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__9_value) as *mut leanh::LeanObject,4907018543776028915 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__11_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__11_value) as *mut leanh::LeanObject,17300771697719127171 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,14861815463019854798 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__0_value) as *mut leanh::LeanObject,8012681890916411767 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__14_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__5_value) as *mut leanh::LeanObject,2268059500047126393 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__2_value) as *mut leanh::LeanObject,11968345501356050016 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__17_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 82, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__16_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__17_value) as *mut leanh::LeanObject,3249143867120583191 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__18_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_validateOptionSimprocSyntax(
    mut v_proc_x3f_680_: *mut leanh::LeanObject,
    mut v_a_681_: *mut leanh::LeanObject,
    mut v_a_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut v_unused_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_699_: u8 = 0;
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_proc_x3f_680_) == 1 {
                    v_val_684_ = leanh::lean_ctor_get(v_proc_x3f_680_, 0);
                    leanh::lean_inc(v_val_684_);
                    leanh::lean_dec_ref_known(v_proc_x3f_680_, 1);
                    v___x_685_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Grind_elabSymSimproc___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___x_685_, 0, v_val_684_);
                    v___x_686_ = l_Lean_Elab_Command_withGrindTacticM___redArg(
                        v___x_685_, v_a_681_, v_a_682_,
                    );
                    if leanh::lean_obj_tag(v___x_686_) == 0 {
                        v_isSharedCheck_694_ = (!leanh::lean_is_exclusive(v___x_686_)) as u8;
                        if v_isSharedCheck_694_ == 0 {
                            v_unused_695_ = leanh::lean_ctor_get(v___x_686_, 0);
                            leanh::lean_dec(v_unused_695_);
                            v___x_688_ = v___x_686_;
                            v_isShared_689_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_686_);
                            v___x_688_ = leanh::lean_box(0);
                            v_isShared_689_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_696_ = leanh::lean_ctor_get(v___x_686_, 0);
                        v_isSharedCheck_703_ = (!leanh::lean_is_exclusive(v___x_686_)) as u8;
                        if v_isSharedCheck_703_ == 0 {
                            v___x_698_ = v___x_686_;
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_696_);
                            leanh::lean_dec(v___x_686_);
                            v___x_698_ = leanh::lean_box(0);
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_proc_x3f_680_);
                    v___x_704_ = leanh::lean_box(0);
                    v___x_705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_705_, 0, v___x_704_);
                    return v___x_705_;
                }
            }
            1 => {
                v___x_690_ = leanh::lean_box(0);
                if v_isShared_689_ == 0 {
                    leanh::lean_ctor_set(v___x_688_, 0, v___x_690_);
                    v___x_692_ = v___x_688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
                    v___x_692_ = v_reuseFailAlloc_693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_692_;
            }
            3 => {
                if v_isShared_699_ == 0 {
                    v___x_701_ = v___x_698_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
                    v___x_701_ = v_reuseFailAlloc_702_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_validateOptionSimprocSyntax___boxed(
    mut v_proc_x3f_706_: *mut leanh::LeanObject,
    mut v_a_707_: *mut leanh::LeanObject,
    mut v_a_708_: *mut leanh::LeanObject,
    mut v_a_709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_710_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_validateOptionSimprocSyntax(v_proc_x3f_706_, v_a_707_, v_a_708_);
    leanh::lean_dec(v_a_708_);
    leanh::lean_dec_ref(v_a_707_);
    return v_res_710_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = leanh::lean_box(1);
    v___x_712_ = l_Lean_MessageData_ofFormat(v___x_711_);
    return v___x_712_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__2;
    v___x_717_ = l_Lean_MessageData_ofFormat(v___x_716_);
    return v___x_717_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5(
    mut v_x_718_: *mut leanh::LeanObject,
    mut v_x_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_724_: u8 = 0;
    let mut v_before_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_728_: u8 = 0;
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_719_) == 0 {
                    return v_x_718_;
                } else {
                    v_head_720_ = leanh::lean_ctor_get(v_x_719_, 0);
                    v_tail_721_ = leanh::lean_ctor_get(v_x_719_, 1);
                    v_isSharedCheck_743_ = (!leanh::lean_is_exclusive(v_x_719_)) as u8;
                    if v_isSharedCheck_743_ == 0 {
                        v___x_723_ = v_x_719_;
                        v_isShared_724_ = v_isSharedCheck_743_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_721_);
                        leanh::lean_inc(v_head_720_);
                        leanh::lean_dec(v_x_719_);
                        v___x_723_ = leanh::lean_box(0);
                        v_isShared_724_ = v_isSharedCheck_743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_725_ = leanh::lean_ctor_get(v_head_720_, 0);
                v_isSharedCheck_741_ = (!leanh::lean_is_exclusive(v_head_720_)) as u8;
                if v_isSharedCheck_741_ == 0 {
                    v_unused_742_ = leanh::lean_ctor_get(v_head_720_, 1);
                    leanh::lean_dec(v_unused_742_);
                    v___x_727_ = v_head_720_;
                    v_isShared_728_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_725_);
                    leanh::lean_dec(v_head_720_);
                    v___x_727_ = leanh::lean_box(0);
                    v_isShared_728_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_729_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_728_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_727_, 7);
                    leanh::lean_ctor_set(v___x_727_, 1, v___x_729_);
                    leanh::lean_ctor_set(v___x_727_, 0, v_x_718_);
                    v___x_731_ = v___x_727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v_x_718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_729_);
                    v___x_731_ = v_reuseFailAlloc_740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_732_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__3);
                if v_isShared_724_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_723_, 7);
                    leanh::lean_ctor_set(v___x_723_, 1, v___x_732_);
                    leanh::lean_ctor_set(v___x_723_, 0, v___x_731_);
                    v___x_734_ = v___x_723_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_732_);
                    v___x_734_ = v_reuseFailAlloc_739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_735_ = l_Lean_MessageData_ofSyntax(v_before_725_);
                v___x_736_ = l_Lean_indentD(v___x_735_);
                v___x_737_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_737_, 0, v___x_734_);
                leanh::lean_ctor_set(v___x_737_, 1, v___x_736_);
                v_x_718_ = v___x_737_;
                v_x_719_ = v_tail_721_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__4(
    mut v_opts_744_: *mut leanh::LeanObject,
    mut v_opt_745_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_746_ = leanh::lean_ctor_get(v_opt_745_, 0);
    v_defValue_747_ = leanh::lean_ctor_get(v_opt_745_, 1);
    v_map_748_ = leanh::lean_ctor_get(v_opts_744_, 0);
    v___x_749_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_748_,
            v_name_746_,
        );
    if leanh::lean_obj_tag(v___x_749_) == 0 {
        let mut v___x_750_: u8 = 0;
        v___x_750_ = (leanh::lean_unbox(v_defValue_747_) as u8);
        return v___x_750_;
    } else {
        let mut v_val_751_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_751_ = leanh::lean_ctor_get(v___x_749_, 0);
        leanh::lean_inc(v_val_751_);
        leanh::lean_dec_ref_known(v___x_749_, 1);
        if leanh::lean_obj_tag(v_val_751_) == 1 {
            let mut v_v_752_: u8 = 0;
            v_v_752_ = leanh::lean_ctor_get_uint8(v_val_751_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_751_, 0);
            return v_v_752_;
        } else {
            let mut v___x_753_: u8 = 0;
            leanh::lean_dec(v_val_751_);
            v___x_753_ = (leanh::lean_unbox(v_defValue_747_) as u8);
            return v___x_753_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_opts_754_: *mut leanh::LeanObject,
    mut v_opt_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: u8 = 0;
    let mut v_r_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__4(v_opts_754_, v_opt_755_);
    leanh::lean_dec_ref(v_opt_755_);
    leanh::lean_dec_ref(v_opts_754_);
    v_r_757_ = leanh::lean_box((v_res_756_) as usize);
    return v_r_757_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
    return v___x_762_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_763_: *mut leanh::LeanObject,
    mut v_macroStack_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v_unused_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_767_ = lean_st_ref_get(v___y_765_);
                v_scopes_768_ = leanh::lean_ctor_get(v___x_767_, 2);
                leanh::lean_inc(v_scopes_768_);
                leanh::lean_dec(v___x_767_);
                v___x_769_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_770_ = l_List_head_x21___redArg(v___x_769_, v_scopes_768_);
                leanh::lean_dec(v_scopes_768_);
                v_opts_771_ = leanh::lean_ctor_get(v___x_770_, 1);
                leanh::lean_inc_ref(v_opts_771_);
                leanh::lean_dec(v___x_770_);
                v___x_772_ = l_Lean_Elab_pp_macroStack;
                v___x_773_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__4(v_opts_771_, v___x_772_);
                leanh::lean_dec_ref(v_opts_771_);
                if v___x_773_ == 0 {
                    leanh::lean_dec(v_macroStack_764_);
                    v___x_774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_774_, 0, v_msgData_763_);
                    return v___x_774_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_764_) == 0 {
                        v___x_775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_775_, 0, v_msgData_763_);
                        return v___x_775_;
                    } else {
                        v_head_776_ = leanh::lean_ctor_get(v_macroStack_764_, 0);
                        leanh::lean_inc(v_head_776_);
                        v_after_777_ = leanh::lean_ctor_get(v_head_776_, 1);
                        v_isSharedCheck_792_ =
                            (!leanh::lean_is_exclusive(v_head_776_)) as u8;
                        if v_isSharedCheck_792_ == 0 {
                            v_unused_793_ = leanh::lean_ctor_get(v_head_776_, 0);
                            leanh::lean_dec(v_unused_793_);
                            v___x_779_ = v_head_776_;
                            v_isShared_780_ = v_isSharedCheck_792_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_777_);
                            leanh::lean_dec(v_head_776_);
                            v___x_779_ = leanh::lean_box(0);
                            v_isShared_780_ = v_isSharedCheck_792_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_781_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_780_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_779_, 7);
                    leanh::lean_ctor_set(v___x_779_, 1, v___x_781_);
                    leanh::lean_ctor_set(v___x_779_, 0, v_msgData_763_);
                    v___x_783_ = v___x_779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_791_, 0, v_msgData_763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_781_);
                    v___x_783_ = v_reuseFailAlloc_791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_784_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_785_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_785_, 0, v___x_783_);
                leanh::lean_ctor_set(v___x_785_, 1, v___x_784_);
                v___x_786_ = l_Lean_MessageData_ofSyntax(v_after_777_);
                v___x_787_ = l_Lean_indentD(v___x_786_);
                v_msgData_788_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_788_, 0, v___x_785_);
                leanh::lean_ctor_set(v_msgData_788_, 1, v___x_787_);
                v___x_789_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2_spec__5(v_msgData_788_, v_macroStack_764_);
                v___x_790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_790_, 0, v___x_789_);
                return v___x_790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_794_: *mut leanh::LeanObject,
    mut v_macroStack_795_: *mut leanh::LeanObject,
    mut v___y_796_: *mut leanh::LeanObject,
    mut v___y_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg(v_msgData_794_, v_macroStack_795_, v___y_796_);
    leanh::lean_dec(v___y_796_);
    return v_res_798_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_799_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_801_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_801_, 0, v___x_800_);
    return v___x_801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_803_ = leanh::lean_unsigned_to_nat(0);
    v___x_804_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_804_, 0, v___x_803_);
    leanh::lean_ctor_set(v___x_804_, 1, v___x_803_);
    leanh::lean_ctor_set(v___x_804_, 2, v___x_803_);
    leanh::lean_ctor_set(v___x_804_, 3, v___x_803_);
    leanh::lean_ctor_set(v___x_804_, 4, v___x_802_);
    leanh::lean_ctor_set(v___x_804_, 5, v___x_802_);
    leanh::lean_ctor_set(v___x_804_, 6, v___x_802_);
    leanh::lean_ctor_set(v___x_804_, 7, v___x_802_);
    leanh::lean_ctor_set(v___x_804_, 8, v___x_802_);
    leanh::lean_ctor_set(v___x_804_, 9, v___x_802_);
    return v___x_804_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = leanh::lean_unsigned_to_nat(32);
    v___x_806_ = lean_mk_empty_array_with_capacity(v___x_805_);
    v___x_807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_807_, 0, v___x_806_);
    return v___x_807_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_808_: usize = 0;
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_808_ = 5usize;
    v___x_809_ = leanh::lean_unsigned_to_nat(0);
    v___x_810_ = leanh::lean_unsigned_to_nat(32);
    v___x_811_ = lean_mk_empty_array_with_capacity(v___x_810_);
    v___x_812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_813_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_813_, 0, v___x_812_);
    leanh::lean_ctor_set(v___x_813_, 1, v___x_811_);
    leanh::lean_ctor_set(v___x_813_, 2, v___x_809_);
    leanh::lean_ctor_set(v___x_813_, 3, v___x_809_);
    leanh::lean_ctor_set_usize(v___x_813_, 4, v___x_808_);
    return v___x_813_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = leanh::lean_box(1);
    v___x_815_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_817_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_817_, 0, v___x_816_);
    leanh::lean_ctor_set(v___x_817_, 1, v___x_815_);
    leanh::lean_ctor_set(v___x_817_, 2, v___x_814_);
    return v___x_817_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_818_: *mut leanh::LeanObject,
    mut v___y_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = lean_st_ref_get(v___y_819_);
    v_env_822_ = leanh::lean_ctor_get(v___x_821_, 0);
    leanh::lean_inc_ref(v_env_822_);
    leanh::lean_dec(v___x_821_);
    v___x_823_ = lean_st_ref_get(v___y_819_);
    v_scopes_824_ = leanh::lean_ctor_get(v___x_823_, 2);
    leanh::lean_inc(v_scopes_824_);
    leanh::lean_dec(v___x_823_);
    v___x_825_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_826_ = l_List_head_x21___redArg(v___x_825_, v_scopes_824_);
    leanh::lean_dec(v_scopes_824_);
    v_opts_827_ = leanh::lean_ctor_get(v___x_826_, 1);
    leanh::lean_inc_ref(v_opts_827_);
    leanh::lean_dec(v___x_826_);
    v___x_828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__2);
    v___x_829_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___closed__5);
    v___x_830_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_830_, 0, v_env_822_);
    leanh::lean_ctor_set(v___x_830_, 1, v___x_828_);
    leanh::lean_ctor_set(v___x_830_, 2, v___x_829_);
    leanh::lean_ctor_set(v___x_830_, 3, v_opts_827_);
    v___x_831_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_831_, 0, v___x_830_);
    leanh::lean_ctor_set(v___x_831_, 1, v_msgData_818_);
    v___x_832_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
    return v___x_832_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_833_: *mut leanh::LeanObject,
    mut v___y_834_: *mut leanh::LeanObject,
    mut v___y_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg(v_msgData_833_, v___y_834_);
    leanh::lean_dec(v___y_834_);
    return v_res_836_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___redArg(
    mut v_msg_837_: *mut leanh::LeanObject,
    mut v___y_838_: *mut leanh::LeanObject,
    mut v___y_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_856_: u8 = 0;
    let mut v_a_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_841_ = l_Lean_Elab_Command_getRef___redArg(v___y_838_);
                if leanh::lean_obj_tag(v___x_841_) == 0 {
                    v_a_842_ = leanh::lean_ctor_get(v___x_841_, 0);
                    leanh::lean_inc(v_a_842_);
                    leanh::lean_dec_ref_known(v___x_841_, 1);
                    v_macroStack_843_ = leanh::lean_ctor_get(v___y_838_, 4);
                    v___x_844_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg(v_msg_837_, v___y_839_);
                    v_a_845_ = leanh::lean_ctor_get(v___x_844_, 0);
                    leanh::lean_inc(v_a_845_);
                    leanh::lean_dec_ref(v___x_844_);
                    v___x_846_ = l_Lean_Elab_getBetterRef(v_a_842_, v_macroStack_843_);
                    leanh::lean_dec(v_a_842_);
                    leanh::lean_inc(v_macroStack_843_);
                    v___x_847_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg(v_a_845_, v_macroStack_843_, v___y_839_);
                    v_a_848_ = leanh::lean_ctor_get(v___x_847_, 0);
                    v_isSharedCheck_856_ = (!leanh::lean_is_exclusive(v___x_847_)) as u8;
                    if v_isSharedCheck_856_ == 0 {
                        v___x_850_ = v___x_847_;
                        v_isShared_851_ = v_isSharedCheck_856_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_848_);
                        leanh::lean_dec(v___x_847_);
                        v___x_850_ = leanh::lean_box(0);
                        v_isShared_851_ = v_isSharedCheck_856_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_837_);
                    v_a_857_ = leanh::lean_ctor_get(v___x_841_, 0);
                    v_isSharedCheck_864_ = (!leanh::lean_is_exclusive(v___x_841_)) as u8;
                    if v_isSharedCheck_864_ == 0 {
                        v___x_859_ = v___x_841_;
                        v_isShared_860_ = v_isSharedCheck_864_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_857_);
                        leanh::lean_dec(v___x_841_);
                        v___x_859_ = leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_852_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_852_, 0, v___x_846_);
                leanh::lean_ctor_set(v___x_852_, 1, v_a_848_);
                if v_isShared_851_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_850_, 1);
                    leanh::lean_ctor_set(v___x_850_, 0, v___x_852_);
                    v___x_854_ = v___x_850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
                    v___x_854_ = v_reuseFailAlloc_855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_854_;
            }
            3 => {
                if v_isShared_860_ == 0 {
                    v___x_862_ = v___x_859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___redArg___boxed(
    mut v_msg_865_: *mut leanh::LeanObject,
    mut v___y_866_: *mut leanh::LeanObject,
    mut v___y_867_: *mut leanh::LeanObject,
    mut v___y_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___redArg(v_msg_865_, v___y_866_, v___y_867_);
    leanh::lean_dec(v___y_867_);
    leanh::lean_dec_ref(v___y_866_);
    return v_res_869_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(
    mut v_ref_870_: *mut leanh::LeanObject,
    mut v_msg_871_: *mut leanh::LeanObject,
    mut v___y_872_: *mut leanh::LeanObject,
    mut v___y_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_886_: u8 = 0;
    let mut v_ref_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_875_ = l_Lean_Elab_Command_getRef___redArg(v___y_872_);
                if leanh::lean_obj_tag(v___x_875_) == 0 {
                    v_a_876_ = leanh::lean_ctor_get(v___x_875_, 0);
                    leanh::lean_inc(v_a_876_);
                    leanh::lean_dec_ref_known(v___x_875_, 1);
                    v_fileName_877_ = leanh::lean_ctor_get(v___y_872_, 0);
                    v_fileMap_878_ = leanh::lean_ctor_get(v___y_872_, 1);
                    v_currRecDepth_879_ = leanh::lean_ctor_get(v___y_872_, 2);
                    v_cmdPos_880_ = leanh::lean_ctor_get(v___y_872_, 3);
                    v_macroStack_881_ = leanh::lean_ctor_get(v___y_872_, 4);
                    v_quotContext_x3f_882_ = leanh::lean_ctor_get(v___y_872_, 5);
                    v_currMacroScope_883_ = leanh::lean_ctor_get(v___y_872_, 6);
                    v_snap_x3f_884_ = leanh::lean_ctor_get(v___y_872_, 8);
                    v_cancelTk_x3f_885_ = leanh::lean_ctor_get(v___y_872_, 9);
                    v_suppressElabErrors_886_ = leanh::lean_ctor_get_uint8(
                        v___y_872_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_887_ = l_Lean_replaceRef(v_ref_870_, v_a_876_);
                    leanh::lean_dec(v_a_876_);
                    leanh::lean_inc(v_cancelTk_x3f_885_);
                    leanh::lean_inc(v_snap_x3f_884_);
                    leanh::lean_inc(v_currMacroScope_883_);
                    leanh::lean_inc(v_quotContext_x3f_882_);
                    leanh::lean_inc(v_macroStack_881_);
                    leanh::lean_inc(v_cmdPos_880_);
                    leanh::lean_inc(v_currRecDepth_879_);
                    leanh::lean_inc_ref(v_fileMap_878_);
                    leanh::lean_inc_ref(v_fileName_877_);
                    v___x_888_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v___x_888_, 0, v_fileName_877_);
                    leanh::lean_ctor_set(v___x_888_, 1, v_fileMap_878_);
                    leanh::lean_ctor_set(v___x_888_, 2, v_currRecDepth_879_);
                    leanh::lean_ctor_set(v___x_888_, 3, v_cmdPos_880_);
                    leanh::lean_ctor_set(v___x_888_, 4, v_macroStack_881_);
                    leanh::lean_ctor_set(v___x_888_, 5, v_quotContext_x3f_882_);
                    leanh::lean_ctor_set(v___x_888_, 6, v_currMacroScope_883_);
                    leanh::lean_ctor_set(v___x_888_, 7, v_ref_887_);
                    leanh::lean_ctor_set(v___x_888_, 8, v_snap_x3f_884_);
                    leanh::lean_ctor_set(v___x_888_, 9, v_cancelTk_x3f_885_);
                    leanh::lean_ctor_set_uint8(
                        v___x_888_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_886_,
                    );
                    v___x_889_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___redArg(v_msg_871_, v___x_888_, v___y_873_);
                    leanh::lean_dec_ref_known(v___x_888_, 10);
                    return v___x_889_;
                } else {
                    leanh::lean_dec_ref(v_msg_871_);
                    v_a_890_ = leanh::lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_897_ = (!leanh::lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_892_ = v___x_875_;
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_890_);
                        leanh::lean_dec(v___x_875_);
                        v___x_892_ = leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg___boxed(
    mut v_ref_898_: *mut leanh::LeanObject,
    mut v_msg_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
    mut v___y_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_ref_898_, v_msg_899_, v___y_900_, v___y_901_);
    leanh::lean_dec(v___y_901_);
    leanh::lean_dec_ref(v___y_900_);
    leanh::lean_dec(v_ref_898_);
    return v_res_903_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__11;
    v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
    return v___x_933_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__13;
    v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
    return v___x_936_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__15;
    v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
    return v___x_939_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__17;
    v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
    return v___x_942_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__21;
    v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1(
    mut v_as_949_: *mut leanh::LeanObject,
    mut v_sz_950_: usize,
    mut v_i_951_: usize,
    mut v_b_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_961_: u8 = 0;
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_968_: u8 = 0;
    let mut v_fst_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_972_: u8 = 0;
    let mut v_fst_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v_a_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1001_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1005_: u8 = 0;
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1020_: u8 = 0;
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1045_: u8 = 0;
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1071_: u8 = 0;
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1077_: u8 = 0;
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1081_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1092_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1136_: u8 = 0;
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_unused_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_unused_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_961_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
                if v___x_961_ == 0 {
                    v___x_962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_962_, 0, v_b_952_);
                    return v___x_962_;
                } else {
                    v_snd_963_ = leanh::lean_ctor_get(v_b_952_, 1);
                    leanh::lean_inc(v_snd_963_);
                    v_snd_964_ = leanh::lean_ctor_get(v_snd_963_, 1);
                    leanh::lean_inc(v_snd_964_);
                    v_fst_965_ = leanh::lean_ctor_get(v_b_952_, 0);
                    v_isSharedCheck_1140_ = (!leanh::lean_is_exclusive(v_b_952_)) as u8;
                    if v_isSharedCheck_1140_ == 0 {
                        v_unused_1141_ = leanh::lean_ctor_get(v_b_952_, 1);
                        leanh::lean_dec(v_unused_1141_);
                        v___x_967_ = v_b_952_;
                        v_isShared_968_ = v_isSharedCheck_1140_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_965_);
                        leanh::lean_dec(v_b_952_);
                        v___x_967_ = leanh::lean_box(0);
                        v_isShared_968_ = v_isSharedCheck_1140_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_958_ = 1usize;
                v___x_959_ = lean_usize_add(v_i_951_, v___x_958_);
                v_i_951_ = v___x_959_;
                v_b_952_ = v_a_957_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_969_ = leanh::lean_ctor_get(v_snd_963_, 0);
                v_isSharedCheck_1138_ = (!leanh::lean_is_exclusive(v_snd_963_)) as u8;
                if v_isSharedCheck_1138_ == 0 {
                    v_unused_1139_ = leanh::lean_ctor_get(v_snd_963_, 1);
                    leanh::lean_dec(v_unused_1139_);
                    v___x_971_ = v_snd_963_;
                    v_isShared_972_ = v_isSharedCheck_1138_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_969_);
                    leanh::lean_dec(v_snd_963_);
                    v___x_971_ = leanh::lean_box(0);
                    v_isShared_972_ = v_isSharedCheck_1138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_973_ = leanh::lean_ctor_get(v_snd_964_, 0);
                v_snd_974_ = leanh::lean_ctor_get(v_snd_964_, 1);
                v_isSharedCheck_1137_ = (!leanh::lean_is_exclusive(v_snd_964_)) as u8;
                if v_isSharedCheck_1137_ == 0 {
                    v___x_976_ = v_snd_964_;
                    v_isShared_977_ = v_isSharedCheck_1137_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_974_);
                    leanh::lean_inc(v_fst_973_);
                    leanh::lean_dec(v_snd_964_);
                    v___x_976_ = leanh::lean_box(0);
                    v_isShared_977_ = v_isSharedCheck_1137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_978_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
                v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__4;
                leanh::lean_inc(v_a_978_);
                v___x_980_ = l_Lean_Syntax_isOfKind(v_a_978_, v___x_979_);
                if v___x_980_ == 0 {
                    v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__6;
                    leanh::lean_inc(v_a_978_);
                    v___x_982_ = l_Lean_Syntax_isOfKind(v_a_978_, v___x_981_);
                    if v___x_982_ == 0 {
                        v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__8;
                        leanh::lean_inc(v_a_978_);
                        v___x_984_ = l_Lean_Syntax_isOfKind(v_a_978_, v___x_983_);
                        if v___x_984_ == 0 {
                            v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__10;
                            leanh::lean_inc(v_a_978_);
                            v___x_986_ = l_Lean_Syntax_isOfKind(v_a_978_, v___x_985_);
                            if v___x_986_ == 0 {
                                v___x_987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12);
                                v___x_988_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_987_, v___y_953_, v___y_954_);
                                if leanh::lean_obj_tag(v___x_988_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_988_, 1);
                                    if v_isShared_977_ == 0 {
                                        v___x_990_ = v___x_976_;
                                        state = 5;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_997_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_997_,
                                            0,
                                            v_fst_973_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_997_,
                                            1,
                                            v_snd_974_,
                                        );
                                        v___x_990_ = v_reuseFailAlloc_997_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_976_);
                                    leanh::lean_dec(v_snd_974_);
                                    leanh::lean_dec(v_fst_973_);
                                    leanh::lean_del_object(v___x_971_);
                                    leanh::lean_dec(v_fst_969_);
                                    leanh::lean_del_object(v___x_967_);
                                    leanh::lean_dec(v_fst_965_);
                                    v_a_998_ = leanh::lean_ctor_get(v___x_988_, 0);
                                    v_isSharedCheck_1005_ =
                                        (!leanh::lean_is_exclusive(v___x_988_)) as u8;
                                    if v_isSharedCheck_1005_ == 0 {
                                        v___x_1000_ = v___x_988_;
                                        v_isShared_1001_ = v_isSharedCheck_1005_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_998_);
                                        leanh::lean_dec(v___x_988_);
                                        v___x_1000_ = leanh::lean_box(0);
                                        v_isShared_1001_ = v_isSharedCheck_1005_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_1006_ = leanh::lean_unsigned_to_nat(2);
                                v___x_1007_ = l_Lean_Syntax_getArg(v_a_978_, v___x_1006_);
                                if leanh::lean_obj_tag(v_fst_969_) == 0 {
                                    v___y_1020_ = v___x_986_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v_fst_969_, 1);
                                    v___y_1020_ = v___x_984_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1031_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1032_ = l_Lean_Syntax_getArg(v_a_978_, v___x_1031_);
                            if leanh::lean_obj_tag(v_fst_965_) == 0 {
                                v___y_1045_ = v___x_984_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_fst_965_, 1);
                                v___y_1045_ = v___x_982_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        v___x_1056_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1057_ = l_Lean_Syntax_getArg(v_a_978_, v___x_1056_);
                        v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__20;
                        leanh::lean_inc(v___x_1057_);
                        v___x_1083_ = l_Lean_Syntax_isOfKind(v___x_1057_, v___x_1082_);
                        if v___x_1083_ == 0 {
                            leanh::lean_dec(v___x_1057_);
                            leanh::lean_del_object(v___x_976_);
                            leanh::lean_del_object(v___x_971_);
                            leanh::lean_del_object(v___x_967_);
                            v___x_1084_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12);
                            v___x_1085_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1084_, v___y_953_, v___y_954_);
                            if leanh::lean_obj_tag(v___x_1085_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1085_, 1);
                                v___x_1086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1086_, 0, v_fst_973_);
                                leanh::lean_ctor_set(v___x_1086_, 1, v_snd_974_);
                                v___x_1087_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1087_, 0, v_fst_969_);
                                leanh::lean_ctor_set(v___x_1087_, 1, v___x_1086_);
                                v___x_1088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1088_, 0, v_fst_965_);
                                leanh::lean_ctor_set(v___x_1088_, 1, v___x_1087_);
                                v_a_957_ = v___x_1088_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_snd_974_);
                                leanh::lean_dec(v_fst_973_);
                                leanh::lean_dec(v_fst_969_);
                                leanh::lean_dec(v_fst_965_);
                                v_a_1089_ = leanh::lean_ctor_get(v___x_1085_, 0);
                                v_isSharedCheck_1096_ =
                                    (!leanh::lean_is_exclusive(v___x_1085_)) as u8;
                                if v_isSharedCheck_1096_ == 0 {
                                    v___x_1091_ = v___x_1085_;
                                    v_isShared_1092_ = v_isSharedCheck_1096_;
                                    state = 31;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1089_);
                                    leanh::lean_dec(v___x_1085_);
                                    v___x_1091_ = leanh::lean_box(0);
                                    v_isShared_1092_ = v_isSharedCheck_1096_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_snd_974_) == 0 {
                                v___y_1071_ = v___x_1083_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_snd_974_, 1);
                                v___y_1071_ = v___x_980_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1097_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1098_ = l_Lean_Syntax_getArg(v_a_978_, v___x_1097_);
                    v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__20;
                    leanh::lean_inc(v___x_1098_);
                    v___x_1123_ = l_Lean_Syntax_isOfKind(v___x_1098_, v___x_1122_);
                    if v___x_1123_ == 0 {
                        leanh::lean_dec(v___x_1098_);
                        leanh::lean_del_object(v___x_976_);
                        leanh::lean_del_object(v___x_971_);
                        leanh::lean_del_object(v___x_967_);
                        v___x_1124_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__12);
                        v___x_1125_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1124_, v___y_953_, v___y_954_);
                        if leanh::lean_obj_tag(v___x_1125_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1125_, 1);
                            v___x_1126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1126_, 0, v_fst_973_);
                            leanh::lean_ctor_set(v___x_1126_, 1, v_snd_974_);
                            v___x_1127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1127_, 0, v_fst_969_);
                            leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
                            v___x_1128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1128_, 0, v_fst_965_);
                            leanh::lean_ctor_set(v___x_1128_, 1, v___x_1127_);
                            v_a_957_ = v___x_1128_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_snd_974_);
                            leanh::lean_dec(v_fst_973_);
                            leanh::lean_dec(v_fst_969_);
                            leanh::lean_dec(v_fst_965_);
                            v_a_1129_ = leanh::lean_ctor_get(v___x_1125_, 0);
                            v_isSharedCheck_1136_ =
                                (!leanh::lean_is_exclusive(v___x_1125_)) as u8;
                            if v_isSharedCheck_1136_ == 0 {
                                v___x_1131_ = v___x_1125_;
                                v_isShared_1132_ = v_isSharedCheck_1136_;
                                state = 40;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1129_);
                                leanh::lean_dec(v___x_1125_);
                                v___x_1131_ = leanh::lean_box(0);
                                v_isShared_1132_ = v_isSharedCheck_1136_;
                                state = 40;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_fst_973_) == 0 {
                            if v___x_1123_ == 0 {
                                state = 37;
                                continue;
                            } else {
                                state = 33;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_fst_973_, 1);
                            state = 37;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 1, v___x_990_);
                    v___x_992_ = v___x_971_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_996_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_996_, 0, v_fst_969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_990_);
                    v___x_992_ = v_reuseFailAlloc_996_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_968_ == 0 {
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_992_);
                    v___x_994_ = v___x_967_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_995_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_995_, 0, v_fst_965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
                    v___x_994_ = v_reuseFailAlloc_995_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_957_ = v___x_994_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_1001_ == 0 {
                    v___x_1003_ = v___x_1000_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
                    v___x_1003_ = v_reuseFailAlloc_1004_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1003_;
            }
            10 => {
                v___x_1009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1009_, 0, v___x_1007_);
                if v_isShared_977_ == 0 {
                    v___x_1011_ = v___x_976_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_fst_973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_snd_974_);
                    v___x_1011_ = v_reuseFailAlloc_1018_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 1, v___x_1011_);
                    leanh::lean_ctor_set(v___x_971_, 0, v___x_1009_);
                    v___x_1013_ = v___x_971_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1017_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1011_);
                    v___x_1013_ = v_reuseFailAlloc_1017_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_968_ == 0 {
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_1013_);
                    v___x_1015_ = v___x_967_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_fst_965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
                    v___x_1015_ = v_reuseFailAlloc_1016_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_957_ = v___x_1015_;
                state = 1;
                continue;
            }
            14 => {
                if v___y_1020_ == 0 {
                    v___x_1021_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__14);
                    v___x_1022_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1021_, v___y_953_, v___y_954_);
                    if leanh::lean_obj_tag(v___x_1022_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1022_, 1);
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1007_);
                        leanh::lean_del_object(v___x_976_);
                        leanh::lean_dec(v_snd_974_);
                        leanh::lean_dec(v_fst_973_);
                        leanh::lean_del_object(v___x_971_);
                        leanh::lean_del_object(v___x_967_);
                        leanh::lean_dec(v_fst_965_);
                        v_a_1023_ = leanh::lean_ctor_get(v___x_1022_, 0);
                        v_isSharedCheck_1030_ =
                            (!leanh::lean_is_exclusive(v___x_1022_)) as u8;
                        if v_isSharedCheck_1030_ == 0 {
                            v___x_1025_ = v___x_1022_;
                            v_isShared_1026_ = v_isSharedCheck_1030_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1023_);
                            leanh::lean_dec(v___x_1022_);
                            v___x_1025_ = leanh::lean_box(0);
                            v_isShared_1026_ = v_isSharedCheck_1030_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            15 => {
                if v_isShared_1026_ == 0 {
                    v___x_1028_ = v___x_1025_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
                    v___x_1028_ = v_reuseFailAlloc_1029_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1028_;
            }
            17 => {
                v___x_1034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1034_, 0, v___x_1032_);
                if v_isShared_977_ == 0 {
                    v___x_1036_ = v___x_976_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_fst_973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_snd_974_);
                    v___x_1036_ = v_reuseFailAlloc_1043_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 1, v___x_1036_);
                    v___x_1038_ = v___x_971_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_fst_969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1036_);
                    v___x_1038_ = v_reuseFailAlloc_1042_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_968_ == 0 {
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_1038_);
                    leanh::lean_ctor_set(v___x_967_, 0, v___x_1034_);
                    v___x_1040_ = v___x_967_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1041_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1038_);
                    v___x_1040_ = v_reuseFailAlloc_1041_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_a_957_ = v___x_1040_;
                state = 1;
                continue;
            }
            21 => {
                if v___y_1045_ == 0 {
                    v___x_1046_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__16);
                    v___x_1047_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1046_, v___y_953_, v___y_954_);
                    if leanh::lean_obj_tag(v___x_1047_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1047_, 1);
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1032_);
                        leanh::lean_del_object(v___x_976_);
                        leanh::lean_dec(v_snd_974_);
                        leanh::lean_dec(v_fst_973_);
                        leanh::lean_del_object(v___x_971_);
                        leanh::lean_dec(v_fst_969_);
                        leanh::lean_del_object(v___x_967_);
                        v_a_1048_ = leanh::lean_ctor_get(v___x_1047_, 0);
                        v_isSharedCheck_1055_ =
                            (!leanh::lean_is_exclusive(v___x_1047_)) as u8;
                        if v_isSharedCheck_1055_ == 0 {
                            v___x_1050_ = v___x_1047_;
                            v_isShared_1051_ = v_isSharedCheck_1055_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1048_);
                            leanh::lean_dec(v___x_1047_);
                            v___x_1050_ = leanh::lean_box(0);
                            v_isShared_1051_ = v_isSharedCheck_1055_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    state = 17;
                    continue;
                }
            }
            22 => {
                if v_isShared_1051_ == 0 {
                    v___x_1053_ = v___x_1050_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
                    v___x_1053_ = v_reuseFailAlloc_1054_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1053_;
            }
            24 => {
                v___x_1059_ = l_Lean_TSyntax_getNat(v___x_1057_);
                leanh::lean_dec(v___x_1057_);
                v___x_1060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1060_, 0, v___x_1059_);
                if v_isShared_977_ == 0 {
                    leanh::lean_ctor_set(v___x_976_, 1, v___x_1060_);
                    v___x_1062_ = v___x_976_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_fst_973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1060_);
                    v___x_1062_ = v_reuseFailAlloc_1069_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 1, v___x_1062_);
                    v___x_1064_ = v___x_971_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1068_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_fst_969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1062_);
                    v___x_1064_ = v_reuseFailAlloc_1068_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_968_ == 0 {
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_1064_);
                    v___x_1066_ = v___x_967_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_fst_965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1064_);
                    v___x_1066_ = v_reuseFailAlloc_1067_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v_a_957_ = v___x_1066_;
                state = 1;
                continue;
            }
            28 => {
                if v___y_1071_ == 0 {
                    v___x_1072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__18);
                    v___x_1073_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1072_, v___y_953_, v___y_954_);
                    if leanh::lean_obj_tag(v___x_1073_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1073_, 1);
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1057_);
                        leanh::lean_del_object(v___x_976_);
                        leanh::lean_dec(v_fst_973_);
                        leanh::lean_del_object(v___x_971_);
                        leanh::lean_dec(v_fst_969_);
                        leanh::lean_del_object(v___x_967_);
                        leanh::lean_dec(v_fst_965_);
                        v_a_1074_ = leanh::lean_ctor_get(v___x_1073_, 0);
                        v_isSharedCheck_1081_ =
                            (!leanh::lean_is_exclusive(v___x_1073_)) as u8;
                        if v_isSharedCheck_1081_ == 0 {
                            v___x_1076_ = v___x_1073_;
                            v_isShared_1077_ = v_isSharedCheck_1081_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1074_);
                            leanh::lean_dec(v___x_1073_);
                            v___x_1076_ = leanh::lean_box(0);
                            v_isShared_1077_ = v_isSharedCheck_1081_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    state = 24;
                    continue;
                }
            }
            29 => {
                if v_isShared_1077_ == 0 {
                    v___x_1079_ = v___x_1076_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1080_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
                    v___x_1079_ = v_reuseFailAlloc_1080_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1079_;
            }
            31 => {
                if v_isShared_1092_ == 0 {
                    v___x_1094_ = v___x_1091_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1094_;
            }
            33 => {
                v___x_1100_ = l_Lean_TSyntax_getNat(v___x_1098_);
                leanh::lean_dec(v___x_1098_);
                v___x_1101_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1101_, 0, v___x_1100_);
                if v_isShared_977_ == 0 {
                    leanh::lean_ctor_set(v___x_976_, 0, v___x_1101_);
                    v___x_1103_ = v___x_976_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_974_);
                    v___x_1103_ = v_reuseFailAlloc_1110_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 1, v___x_1103_);
                    v___x_1105_ = v___x_971_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_fst_969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1103_);
                    v___x_1105_ = v_reuseFailAlloc_1109_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_968_ == 0 {
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_1105_);
                    v___x_1107_ = v___x_967_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1105_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v_a_957_ = v___x_1107_;
                state = 1;
                continue;
            }
            37 => {
                v___x_1112_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___closed__22);
                v___x_1113_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_a_978_, v___x_1112_, v___y_953_, v___y_954_);
                if leanh::lean_obj_tag(v___x_1113_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1113_, 1);
                    state = 33;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1098_);
                    leanh::lean_del_object(v___x_976_);
                    leanh::lean_dec(v_snd_974_);
                    leanh::lean_del_object(v___x_971_);
                    leanh::lean_dec(v_fst_969_);
                    leanh::lean_del_object(v___x_967_);
                    leanh::lean_dec(v_fst_965_);
                    v_a_1114_ = leanh::lean_ctor_get(v___x_1113_, 0);
                    v_isSharedCheck_1121_ = (!leanh::lean_is_exclusive(v___x_1113_)) as u8;
                    if v_isSharedCheck_1121_ == 0 {
                        v___x_1116_ = v___x_1113_;
                        v_isShared_1117_ = v_isSharedCheck_1121_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1114_);
                        leanh::lean_dec(v___x_1113_);
                        v___x_1116_ = leanh::lean_box(0);
                        v_isShared_1117_ = v_isSharedCheck_1121_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                if v_isShared_1117_ == 0 {
                    v___x_1119_ = v___x_1116_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
                    v___x_1119_ = v_reuseFailAlloc_1120_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1119_;
            }
            40 => {
                if v_isShared_1132_ == 0 {
                    v___x_1134_ = v___x_1131_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
                    v___x_1134_ = v_reuseFailAlloc_1135_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1___boxed(
    mut v_as_1142_: *mut leanh::LeanObject,
    mut v_sz_1143_: *mut leanh::LeanObject,
    mut v_i_1144_: *mut leanh::LeanObject,
    mut v_b_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1149_: usize = 0;
    let mut v_i_boxed_1150_: usize = 0;
    let mut v_res_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1149_ = leanh::lean_unbox_usize(v_sz_1143_);
    leanh::lean_dec(v_sz_1143_);
    v_i_boxed_1150_ = leanh::lean_unbox_usize(v_i_1144_);
    leanh::lean_dec(v_i_1144_);
    v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1(v_as_1142_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1145_, v___y_1146_, v___y_1147_);
    leanh::lean_dec(v___y_1147_);
    leanh::lean_dec_ref(v___y_1146_);
    leanh::lean_dec_ref(v_as_1142_);
    return v_res_1151_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__3;
    v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
    return v___x_1162_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__5;
    v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
    return v___x_1165_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp(
    mut v_stx_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_a_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1195_: u8 = 0;
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut v___y_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1223_: usize = 0;
    let mut v___x_1224_: usize = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1245_: u8 = 0;
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1170_ = lean_st_ref_get(v_a_1168_);
                v_env_1171_ = leanh::lean_ctor_get(v___x_1170_, 0);
                leanh::lean_inc_ref(v_env_1171_);
                leanh::lean_dec(v___x_1170_);
                v___x_1172_ = leanh::lean_unsigned_to_nat(1);
                v_id_1173_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1172_);
                v_name_1174_ = l_Lean_Syntax_getId(v_id_1173_);
                v___x_1246_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_1171_, v_name_1174_);
                if leanh::lean_obj_tag(v___x_1246_) == 0 {
                    leanh::lean_dec(v_id_1173_);
                    v___y_1217_ = v_a_1167_;
                    v___y_1218_ = v_a_1168_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_1246_, 1);
                    v___x_1247_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4_once), _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__4);
                    v___x_1248_ = l_Lean_MessageData_ofName(v_name_1174_);
                    v___x_1249_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1247_);
                    leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
                    v___x_1250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6_once), _init_l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__6);
                    v___x_1251_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1251_, 0, v___x_1249_);
                    leanh::lean_ctor_set(v___x_1251_, 1, v___x_1250_);
                    v___x_1252_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_id_1173_, v___x_1251_, v_a_1167_, v_a_1168_);
                    leanh::lean_dec(v_id_1173_);
                    return v___x_1252_;
                }
            }
            1 => {
                v___x_1181_ = lean_st_ref_take(v___y_1177_);
                v_env_1182_ = leanh::lean_ctor_get(v___x_1181_, 0);
                v_messages_1183_ = leanh::lean_ctor_get(v___x_1181_, 1);
                v_scopes_1184_ = leanh::lean_ctor_get(v___x_1181_, 2);
                v_usedQuotCtxts_1185_ = leanh::lean_ctor_get(v___x_1181_, 3);
                v_nextMacroScope_1186_ = leanh::lean_ctor_get(v___x_1181_, 4);
                v_maxRecDepth_1187_ = leanh::lean_ctor_get(v___x_1181_, 5);
                v_ngen_1188_ = leanh::lean_ctor_get(v___x_1181_, 6);
                v_auxDeclNGen_1189_ = leanh::lean_ctor_get(v___x_1181_, 7);
                v_infoState_1190_ = leanh::lean_ctor_get(v___x_1181_, 8);
                v_traceState_1191_ = leanh::lean_ctor_get(v___x_1181_, 9);
                v_snapshotTasks_1192_ = leanh::lean_ctor_get(v___x_1181_, 10);
                v_isSharedCheck_1207_ = (!leanh::lean_is_exclusive(v___x_1181_)) as u8;
                if v_isSharedCheck_1207_ == 0 {
                    v___x_1194_ = v___x_1181_;
                    v_isShared_1195_ = v_isSharedCheck_1207_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1192_);
                    leanh::lean_inc(v_traceState_1191_);
                    leanh::lean_inc(v_infoState_1190_);
                    leanh::lean_inc(v_auxDeclNGen_1189_);
                    leanh::lean_inc(v_ngen_1188_);
                    leanh::lean_inc(v_maxRecDepth_1187_);
                    leanh::lean_inc(v_nextMacroScope_1186_);
                    leanh::lean_inc(v_usedQuotCtxts_1185_);
                    leanh::lean_inc(v_scopes_1184_);
                    leanh::lean_inc(v_messages_1183_);
                    leanh::lean_inc(v_env_1182_);
                    leanh::lean_dec(v___x_1181_);
                    v___x_1194_ = leanh::lean_box(0);
                    v_isShared_1195_ = v_isSharedCheck_1207_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1196_, 0, v___y_1179_);
                leanh::lean_ctor_set(v___x_1196_, 1, v___y_1180_);
                v___x_1197_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1197_, 0, v___y_1176_);
                leanh::lean_ctor_set(v___x_1197_, 1, v___y_1178_);
                leanh::lean_ctor_set(v___x_1197_, 2, v___x_1196_);
                v___x_1198_ = l_Lean_Meta_Sym_Simp_symSimpVariantExtension;
                v___x_1199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1199_, 0, v_name_1174_);
                leanh::lean_ctor_set(v___x_1199_, 1, v___x_1197_);
                v___x_1200_ = l_Lean_ScopedEnvExtension_addEntry___redArg(
                    v___x_1198_,
                    v_env_1182_,
                    v___x_1199_,
                );
                if v_isShared_1195_ == 0 {
                    leanh::lean_ctor_set(v___x_1194_, 0, v___x_1200_);
                    v___x_1202_ = v___x_1194_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_messages_1183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_scopes_1184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_usedQuotCtxts_1185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_nextMacroScope_1186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 5, v_maxRecDepth_1187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_ngen_1188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_auxDeclNGen_1189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_infoState_1190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 9, v_traceState_1191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 10, v_snapshotTasks_1192_);
                    v___x_1202_ = v_reuseFailAlloc_1206_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1203_ = lean_st_ref_set(v___y_1177_, v___x_1202_);
                v___x_1204_ = leanh::lean_box(0);
                v___x_1205_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                return v___x_1205_;
            }
            4 => {
                if leanh::lean_obj_tag(v___y_1211_) == 0 {
                    v___x_1214_ = leanh::lean_unsigned_to_nat(2);
                    v___y_1176_ = v___y_1210_;
                    v___y_1177_ = v___y_1209_;
                    v___y_1178_ = v___y_1212_;
                    v___y_1179_ = v___y_1213_;
                    v___y_1180_ = v___x_1214_;
                    state = 1;
                    continue;
                } else {
                    v_val_1215_ = leanh::lean_ctor_get(v___y_1211_, 0);
                    leanh::lean_inc(v_val_1215_);
                    leanh::lean_dec_ref_known(v___y_1211_, 1);
                    v___y_1176_ = v___y_1210_;
                    v___y_1177_ = v___y_1209_;
                    v___y_1178_ = v___y_1212_;
                    v___y_1179_ = v___y_1213_;
                    v___y_1180_ = v_val_1215_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1219_ = leanh::lean_unsigned_to_nat(3);
                v___x_1220_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1219_);
                v___x_1221_ = l_Lean_Syntax_getArgs(v___x_1220_);
                leanh::lean_dec(v___x_1220_);
                v___x_1222_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___closed__2;
                v_sz_1223_ = lean_array_size(v___x_1221_);
                v___x_1224_ = 0usize;
                v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__1(v___x_1221_, v_sz_1223_, v___x_1224_, v___x_1222_, v___y_1217_, v___y_1218_);
                leanh::lean_dec_ref(v___x_1221_);
                if leanh::lean_obj_tag(v___x_1225_) == 0 {
                    v_a_1226_ = leanh::lean_ctor_get(v___x_1225_, 0);
                    leanh::lean_inc(v_a_1226_);
                    leanh::lean_dec_ref_known(v___x_1225_, 1);
                    v_fst_1227_ = leanh::lean_ctor_get(v_a_1226_, 0);
                    leanh::lean_inc_n(v_fst_1227_, 2);
                    v_snd_1228_ = leanh::lean_ctor_get(v_a_1226_, 1);
                    leanh::lean_inc(v_snd_1228_);
                    leanh::lean_dec(v_a_1226_);
                    v___x_1229_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_validateOptionSimprocSyntax(v_fst_1227_, v___y_1217_, v___y_1218_);
                    if leanh::lean_obj_tag(v___x_1229_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1229_, 1);
                        v_fst_1230_ = leanh::lean_ctor_get(v_snd_1228_, 0);
                        leanh::lean_inc_n(v_fst_1230_, 2);
                        v_snd_1231_ = leanh::lean_ctor_get(v_snd_1228_, 1);
                        leanh::lean_inc(v_snd_1231_);
                        leanh::lean_dec(v_snd_1228_);
                        v___x_1232_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_validateOptionSimprocSyntax(v_fst_1230_, v___y_1217_, v___y_1218_);
                        if leanh::lean_obj_tag(v___x_1232_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1232_, 1);
                            v_fst_1233_ = leanh::lean_ctor_get(v_snd_1231_, 0);
                            if leanh::lean_obj_tag(v_fst_1233_) == 0 {
                                v_snd_1234_ = leanh::lean_ctor_get(v_snd_1231_, 1);
                                leanh::lean_inc(v_snd_1234_);
                                leanh::lean_dec(v_snd_1231_);
                                v___x_1235_ = leanh::lean_unsigned_to_nat(100000);
                                v___y_1209_ = v___y_1218_;
                                v___y_1210_ = v_fst_1227_;
                                v___y_1211_ = v_snd_1234_;
                                v___y_1212_ = v_fst_1230_;
                                v___y_1213_ = v___x_1235_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_fst_1233_);
                                v_snd_1236_ = leanh::lean_ctor_get(v_snd_1231_, 1);
                                leanh::lean_inc(v_snd_1236_);
                                leanh::lean_dec(v_snd_1231_);
                                v_val_1237_ = leanh::lean_ctor_get(v_fst_1233_, 0);
                                leanh::lean_inc(v_val_1237_);
                                leanh::lean_dec_ref_known(v_fst_1233_, 1);
                                v___y_1209_ = v___y_1218_;
                                v___y_1210_ = v_fst_1227_;
                                v___y_1211_ = v_snd_1236_;
                                v___y_1212_ = v_fst_1230_;
                                v___y_1213_ = v_val_1237_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_snd_1231_);
                            leanh::lean_dec(v_fst_1230_);
                            leanh::lean_dec(v_fst_1227_);
                            leanh::lean_dec(v_name_1174_);
                            return v___x_1232_;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1228_);
                        leanh::lean_dec(v_fst_1227_);
                        leanh::lean_dec(v_name_1174_);
                        return v___x_1229_;
                    }
                } else {
                    leanh::lean_dec(v_name_1174_);
                    v_a_1238_ = leanh::lean_ctor_get(v___x_1225_, 0);
                    v_isSharedCheck_1245_ = (!leanh::lean_is_exclusive(v___x_1225_)) as u8;
                    if v_isSharedCheck_1245_ == 0 {
                        v___x_1240_ = v___x_1225_;
                        v_isShared_1241_ = v_isSharedCheck_1245_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1238_);
                        leanh::lean_dec(v___x_1225_);
                        v___x_1240_ = leanh::lean_box(0);
                        v_isShared_1241_ = v_isSharedCheck_1245_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1241_ == 0 {
                    v___x_1243_ = v___x_1240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
                    v___x_1243_ = v_reuseFailAlloc_1244_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___boxed(
    mut v_stx_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ =
        l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp(
            v_stx_1253_,
            v_a_1254_,
            v_a_1255_,
        );
    leanh::lean_dec(v_a_1255_);
    leanh::lean_dec_ref(v_a_1254_);
    leanh::lean_dec(v_stx_1253_);
    return v_res_1257_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0(
    mut v_00_u03b1_1258_: *mut leanh::LeanObject,
    mut v_ref_1259_: *mut leanh::LeanObject,
    mut v_msg_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___redArg(v_ref_1259_, v_msg_1260_, v___y_1261_, v___y_1262_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0___boxed(
    mut v_00_u03b1_1265_: *mut leanh::LeanObject,
    mut v_ref_1266_: *mut leanh::LeanObject,
    mut v_msg_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v___y_1269_: *mut leanh::LeanObject,
    mut v___y_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0(v_00_u03b1_1265_, v_ref_1266_, v_msg_1267_, v___y_1268_, v___y_1269_);
    leanh::lean_dec(v___y_1269_);
    leanh::lean_dec_ref(v___y_1268_);
    leanh::lean_dec(v_ref_1266_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1(
    mut v_msgData_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___redArg(v_msgData_1272_, v___y_1274_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__1(v_msgData_1277_, v___y_1278_, v___y_1279_);
    leanh::lean_dec(v___y_1279_);
    leanh::lean_dec_ref(v___y_1278_);
    return v_res_1281_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0(
    mut v_00_u03b1_1282_: *mut leanh::LeanObject,
    mut v_msg_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___redArg(v_msg_1283_, v___y_1284_, v___y_1285_);
    return v___x_1287_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0___boxed(
    mut v_00_u03b1_1288_: *mut leanh::LeanObject,
    mut v_msg_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
    mut v___y_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0(v_00_u03b1_1288_, v_msg_1289_, v___y_1290_, v___y_1291_);
    leanh::lean_dec(v___y_1291_);
    leanh::lean_dec_ref(v___y_1290_);
    return v_res_1293_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2(
    mut v_msgData_1294_: *mut leanh::LeanObject,
    mut v_macroStack_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___redArg(v_msgData_1294_, v_macroStack_1295_, v___y_1297_);
    return v___x_1299_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_1300_: *mut leanh::LeanObject,
    mut v_macroStack_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp_spec__0_spec__0_spec__2(v_msgData_1300_, v_macroStack_1301_, v___y_1302_, v___y_1303_);
    leanh::lean_dec(v___y_1303_);
    leanh::lean_dec_ref(v___y_1302_);
    return v_res_1305_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1()
-> *mut leanh::LeanObject {
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1353_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__1;
    v___x_1354_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___closed__18;
    v___x_1355_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___boxed as *mut core::ffi::c_void, 4, 0);
    v___x_1356_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1352_,
        v___x_1353_,
        v___x_1354_,
        v___x_1355_,
    );
    return v___x_1356_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1___boxed(
    mut v_a_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1();
    return v_res_1358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_RegisterSymSimp_0__Lean_Elab_Command_elabRegisterSymSimp__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_WithGrindTacticM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(builtin);
}