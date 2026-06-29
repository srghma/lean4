// Lean compiler output
// Module: Lean.Linter.Builtin
// Imports: Lean.Linter.Util Lean.Elab.Command
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [115, 117, 115, 112, 105, 99, 105, 111, 117, 115, 85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 80, 97, 116, 116, 101, 114, 110, 115, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1190709675906190208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 115, 117, 115, 112, 105, 99, 105, 111, 117, 115, 32, 117, 110, 101, 120, 112, 97, 110, 100, 101, 114, 32, 112, 97, 116, 116, 101, 114, 110, 115, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3916942831794082747 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_linter_suspiciousUnexpanderPatterns: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,7499624980761693169 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value: crate::leanh::LeanStringObject<142> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 142, m_capacity: 142, m_length: 141, m_data: [85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 115, 32, 115, 104, 111, 117, 108, 100, 32, 109, 97, 116, 99, 104, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 103, 97, 105, 110, 115, 116, 32, 97, 110, 32, 97, 110, 116, 105, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 96, 36, 95, 96, 32, 115, 111, 32, 97, 115, 32, 116, 111, 32, 98, 101, 32, 105, 110, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 111, 102, 32, 116, 104, 101, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 32, 111, 102, 32, 116, 104, 101, 32, 110, 97, 109, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [113, 117, 111, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,5855146430765573009 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 112, 112, 95, 117, 110, 101, 120, 112, 97, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,1464131427232734893 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8497769072906204829 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14557702332550915328 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        9789339221525904376 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value)
            as *mut crate::leanh::LeanObject,
        5473625859156281626 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 101, 99, 108, 86, 97, 108, 69, 113, 110, 115, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value)
            as *mut crate::leanh::LeanObject,
        2637955643238073017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        109, 97, 116, 99, 104, 65, 108, 116, 115, 87, 104, 101, 114, 101, 68, 101, 99, 108, 115, 0,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value)
            as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value)
            as *mut crate::leanh::LeanObject,
        9063780239635860524 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5496964320310671834 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_suspiciousUnexpanderPatterns: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(
    mut v_name_920_: *mut crate::leanh::LeanObject,
    mut v_decl_921_: *mut crate::leanh::LeanObject,
    mut v_ref_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut v_unused_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_924_ = crate::leanh::lean_ctor_get(v_decl_921_, 0);
                v_descr_925_ = crate::leanh::lean_ctor_get(v_decl_921_, 1);
                v_deprecation_x3f_926_ = crate::leanh::lean_ctor_get(v_decl_921_, 2);
                v___x_927_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_928_ = (crate::leanh::lean_unbox(v_defValue_924_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_927_, 0 as u32, v___x_928_);
                crate::leanh::lean_inc(v_deprecation_x3f_926_);
                crate::leanh::lean_inc_ref(v_descr_925_);
                crate::leanh::lean_inc_n(v_name_920_, 2);
                v___x_929_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_929_, 0, v_name_920_);
                crate::leanh::lean_ctor_set(v___x_929_, 1, v_ref_922_);
                crate::leanh::lean_ctor_set(v___x_929_, 2, v___x_927_);
                crate::leanh::lean_ctor_set(v___x_929_, 3, v_descr_925_);
                crate::leanh::lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_926_);
                v___x_930_ = lean_register_option(v_name_920_, v___x_929_);
                if crate::leanh::lean_obj_tag(v___x_930_) == 0 {
                    v_isSharedCheck_938_ = (!crate::leanh::lean_is_exclusive(v___x_930_)) as u8;
                    if v_isSharedCheck_938_ == 0 {
                        v_unused_939_ = crate::leanh::lean_ctor_get(v___x_930_, 0);
                        crate::leanh::lean_dec(v_unused_939_);
                        v___x_932_ = v___x_930_;
                        v_isShared_933_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_930_);
                        v___x_932_ = crate::leanh::lean_box(0);
                        v_isShared_933_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_920_);
                    v_a_940_ = crate::leanh::lean_ctor_get(v___x_930_, 0);
                    v_isSharedCheck_947_ = (!crate::leanh::lean_is_exclusive(v___x_930_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_942_ = v___x_930_;
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_940_);
                        crate::leanh::lean_dec(v___x_930_);
                        v___x_942_ = crate::leanh::lean_box(0);
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_924_);
                v___x_934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_934_, 0, v_name_920_);
                crate::leanh::lean_ctor_set(v___x_934_, 1, v_defValue_924_);
                if v_isShared_933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_932_, 0, v___x_934_);
                    v___x_936_ = v___x_932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
                    v___x_936_ = v_reuseFailAlloc_937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_936_;
            }
            3 => {
                if v_isShared_943_ == 0 {
                    v___x_945_ = v___x_942_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_948_: *mut crate::leanh::LeanObject,
    mut v_decl_949_: *mut crate::leanh::LeanObject,
    mut v_ref_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
    crate::leanh::lean_dec_ref(v_decl_949_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_973_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_974_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_975_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v___x_972_, v___x_973_, v___x_974_);
    return v___x_975_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(
    mut v_a_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_977_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
    return v_res_977_;
}
pub unsafe fn l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(
    mut v_o_978_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    v___x_979_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
    v___x_980_ = l_Lean_Linter_getLinterValue(v___x_979_, v_o_978_);
    return v___x_980_;
}
pub unsafe fn l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(
    mut v_o_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_981_);
    crate::leanh::lean_dec_ref(v_o_981_);
    v_r_983_ = crate::leanh::lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(
    mut v_o_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_st_ref_get(v___y_985_);
    v_env_988_ = crate::leanh::lean_ctor_get(v___x_987_, 0);
    crate::leanh::lean_inc_ref(v_env_988_);
    crate::leanh::lean_dec(v___x_987_);
    v___x_989_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_990_ = crate::leanh::lean_ctor_get(v___x_989_, 0);
    v_asyncMode_991_ = crate::leanh::lean_ctor_get(v_toEnvExtension_990_, 2);
    v___x_992_ = crate::leanh::lean_box(1);
    v___x_993_ = crate::leanh::lean_box(0);
    v_linterSets_994_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_992_,
        v___x_989_,
        v_env_988_,
        v_asyncMode_991_,
        v___x_993_,
    );
    v___x_995_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_995_, 0, v_o_984_);
    crate::leanh::lean_ctor_set(v___x_995_, 1, v_linterSets_994_);
    v___x_996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_996_, 0, v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(
    mut v_o_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_997_, v___y_998_);
    crate::leanh::lean_dec(v___y_998_);
    return v_res_1000_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_st_ref_get(v___y_1002_);
    v_scopes_1005_ = crate::leanh::lean_ctor_get(v___x_1004_, 2);
    crate::leanh::lean_inc(v_scopes_1005_);
    crate::leanh::lean_dec(v___x_1004_);
    v___x_1006_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1007_ = l_List_head_x21___redArg(v___x_1006_, v_scopes_1005_);
    crate::leanh::lean_dec(v_scopes_1005_);
    v_opts_1008_ = crate::leanh::lean_ctor_get(v___x_1007_, 1);
    crate::leanh::lean_inc_ref(v_opts_1008_);
    crate::leanh::lean_dec(v___x_1007_);
    v___x_1009_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_1008_, v___y_1002_);
    return v___x_1009_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(
            v___y_1010_,
            v___y_1011_,
        );
    crate::leanh::lean_dec(v___y_1011_);
    crate::leanh::lean_dec_ref(v___y_1010_);
    return v_res_1013_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(
    mut v_sz_1028_: usize,
    mut v_i_1029_: usize,
    mut v_bs_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1031_ = lean_usize_dec_lt(v_i_1029_, v_sz_1028_);
                if v___x_1031_ == 0 {
                    v___x_1032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1032_, 0, v_bs_1030_);
                    return v___x_1032_;
                } else {
                    v_v_1033_ = lean_array_uget(v_bs_1030_, v_i_1029_);
                    v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3;
                    crate::leanh::lean_inc(v_v_1033_);
                    v___x_1035_ = l_Lean_Syntax_isOfKind(v_v_1033_, v___x_1034_);
                    if v___x_1035_ == 0 {
                        crate::leanh::lean_dec(v_v_1033_);
                        crate::leanh::lean_dec_ref(v_bs_1030_);
                        v___x_1036_ = crate::leanh::lean_box(0);
                        return v___x_1036_;
                    } else {
                        v___x_1037_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1038_ = l_Lean_Syntax_getArg(v_v_1033_, v___x_1037_);
                        v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5;
                        crate::leanh::lean_inc(v___x_1038_);
                        v___x_1040_ = l_Lean_Syntax_isOfKind(v___x_1038_, v___x_1039_);
                        if v___x_1040_ == 0 {
                            crate::leanh::lean_dec(v___x_1038_);
                            crate::leanh::lean_dec(v_v_1033_);
                            crate::leanh::lean_dec_ref(v_bs_1030_);
                            v___x_1041_ = crate::leanh::lean_box(0);
                            return v___x_1041_;
                        } else {
                            v___x_1042_ = l_Lean_Syntax_getArg(v___x_1038_, v___x_1037_);
                            crate::leanh::lean_dec(v___x_1038_);
                            v___x_1043_ = l_Lean_Syntax_matchesNull(v___x_1042_, v___x_1037_);
                            if v___x_1043_ == 0 {
                                crate::leanh::lean_dec(v_v_1033_);
                                crate::leanh::lean_dec_ref(v_bs_1030_);
                                v___x_1044_ = crate::leanh::lean_box(0);
                                return v___x_1044_;
                            } else {
                                v___x_1045_ = crate::leanh::lean_unsigned_to_nat(1);
                                v_bs_x27_1046_ =
                                    lean_array_uset(v_bs_1030_, v_i_1029_, v___x_1037_);
                                v___x_1047_ = l_Lean_Syntax_getArg(v_v_1033_, v___x_1045_);
                                crate::leanh::lean_dec(v_v_1033_);
                                v___x_1048_ = 1usize;
                                v___x_1049_ = lean_usize_add(v_i_1029_, v___x_1048_);
                                v___x_1050_ =
                                    lean_array_uset(v_bs_x27_1046_, v_i_1029_, v___x_1047_);
                                v_i_1029_ = v___x_1049_;
                                v_bs_1030_ = v___x_1050_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___boxed(
    mut v_sz_1052_: *mut crate::leanh::LeanObject,
    mut v_i_1053_: *mut crate::leanh::LeanObject,
    mut v_bs_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1055_: usize = 0;
    let mut v_i_boxed_1056_: usize = 0;
    let mut v_res_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1055_ = crate::leanh::lean_unbox_usize(v_sz_1052_);
    crate::leanh::lean_dec(v_sz_1052_);
    v_i_boxed_1056_ = crate::leanh::lean_unbox_usize(v_i_1053_);
    crate::leanh::lean_dec(v_i_1053_);
    v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(
    mut v_opts_1058_: *mut crate::leanh::LeanObject,
    mut v_opt_1059_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1060_ = crate::leanh::lean_ctor_get(v_opt_1059_, 0);
    v_defValue_1061_ = crate::leanh::lean_ctor_get(v_opt_1059_, 1);
    v_map_1062_ = crate::leanh::lean_ctor_get(v_opts_1058_, 0);
    v___x_1063_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1062_,
            v_name_1060_,
        );
    if crate::leanh::lean_obj_tag(v___x_1063_) == 0 {
        let mut v___x_1064_: u8 = 0;
        v___x_1064_ = (crate::leanh::lean_unbox(v_defValue_1061_) as u8);
        return v___x_1064_;
    } else {
        let mut v_val_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1065_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
        crate::leanh::lean_inc(v_val_1065_);
        crate::leanh::lean_dec_ref_known(v___x_1063_, 1);
        if crate::leanh::lean_obj_tag(v_val_1065_) == 1 {
            let mut v_v_1066_: u8 = 0;
            v_v_1066_ = crate::leanh::lean_ctor_get_uint8(v_val_1065_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1065_, 0);
            return v_v_1066_;
        } else {
            let mut v___x_1067_: u8 = 0;
            crate::leanh::lean_dec(v_val_1065_);
            v___x_1067_ = (crate::leanh::lean_unbox(v_defValue_1061_) as u8);
            return v___x_1067_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(
    mut v_opts_1068_: *mut crate::leanh::LeanObject,
    mut v_opt_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1070_: u8 = 0;
    let mut v_r_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_1068_, v_opt_1069_);
    crate::leanh::lean_dec_ref(v_opt_1069_);
    crate::leanh::lean_dec_ref(v_opts_1068_);
    v_r_1071_ = crate::leanh::lean_box((v_res_1070_) as usize);
    return v_r_1071_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1072_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
    v___x_1074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
    return v___x_1074_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
    v___x_1076_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1077_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 1, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 2, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 3, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 4, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 5, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 6, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 7, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 8, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 9, v___x_1075_);
    return v___x_1077_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1079_ = lean_mk_empty_array_with_capacity(v___x_1078_);
    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = 5usize;
    v___x_1082_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1083_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1083_);
    v___x_1085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
    v___x_1086_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1086_, 0, v___x_1085_);
    crate::leanh::lean_ctor_set(v___x_1086_, 1, v___x_1084_);
    crate::leanh::lean_ctor_set(v___x_1086_, 2, v___x_1082_);
    crate::leanh::lean_ctor_set(v___x_1086_, 3, v___x_1082_);
    crate::leanh::lean_ctor_set_usize(v___x_1086_, 4, v___x_1081_);
    return v___x_1086_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = crate::leanh::lean_box(1);
    v___x_1088_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
    v___x_1089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
    v___x_1090_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1090_, 0, v___x_1089_);
    crate::leanh::lean_ctor_set(v___x_1090_, 1, v___x_1088_);
    crate::leanh::lean_ctor_set(v___x_1090_, 2, v___x_1087_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(
    mut v_msgData_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = lean_st_ref_get(v___y_1092_);
    v_env_1095_ = crate::leanh::lean_ctor_get(v___x_1094_, 0);
    crate::leanh::lean_inc_ref(v_env_1095_);
    crate::leanh::lean_dec(v___x_1094_);
    v___x_1096_ = lean_st_ref_get(v___y_1092_);
    v_scopes_1097_ = crate::leanh::lean_ctor_get(v___x_1096_, 2);
    crate::leanh::lean_inc(v_scopes_1097_);
    crate::leanh::lean_dec(v___x_1096_);
    v___x_1098_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1099_ = l_List_head_x21___redArg(v___x_1098_, v_scopes_1097_);
    crate::leanh::lean_dec(v_scopes_1097_);
    v_opts_1100_ = crate::leanh::lean_ctor_get(v___x_1099_, 1);
    crate::leanh::lean_inc_ref(v_opts_1100_);
    crate::leanh::lean_dec(v___x_1099_);
    v___x_1101_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
    v___x_1102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
    v___x_1103_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1103_, 0, v_env_1095_);
    crate::leanh::lean_ctor_set(v___x_1103_, 1, v___x_1101_);
    crate::leanh::lean_ctor_set(v___x_1103_, 2, v___x_1102_);
    crate::leanh::lean_ctor_set(v___x_1103_, 3, v_opts_1100_);
    v___x_1104_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    crate::leanh::lean_ctor_set(v___x_1104_, 1, v_msgData_1091_);
    v___x_1105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(
    mut v_msgData_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_1106_, v___y_1107_);
    crate::leanh::lean_dec(v___y_1107_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(
    mut v___y_1111_: u8,
    mut v_suppressElabErrors_1112_: u8,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1113_) == 1 {
        let mut v_pre_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1114_ = crate::leanh::lean_ctor_get(v_x_1113_, 0);
        if crate::leanh::lean_obj_tag(v_pre_1114_) == 0 {
            let mut v_str_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: u8 = 0;
            v_str_1115_ = crate::leanh::lean_ctor_get(v_x_1113_, 1);
            v___x_1116_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0;
            v___x_1117_ = lean_string_dec_eq(v_str_1115_, v___x_1116_);
            if v___x_1117_ == 0 {
                return v___y_1111_;
            } else {
                return v_suppressElabErrors_1112_;
            }
        } else {
            return v___y_1111_;
        }
    } else {
        return v___y_1111_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed(
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1119_: *mut crate::leanh::LeanObject,
    mut v_x_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_26029__boxed_1121_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1122_: u8 = 0;
    let mut v_res_1123_: u8 = 0;
    let mut v_r_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_26029__boxed_1121_ = (crate::leanh::lean_unbox(v___y_1118_) as u8);
    v_suppressElabErrors_boxed_1122_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1119_) as u8);
    v_res_1123_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v___y_26029__boxed_1121_, v_suppressElabErrors_boxed_1122_, v_x_1120_);
    crate::leanh::lean_dec(v_x_1120_);
    v_r_1124_ = crate::leanh::lean_box((v_res_1123_) as usize);
    return v_r_1124_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(
    mut v_ref_1126_: *mut crate::leanh::LeanObject,
    mut v_msgData_1127_: *mut crate::leanh::LeanObject,
    mut v_severity_1128_: u8,
    mut v_isSilent_1129_: u8,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1134_: u8 = 0;
    let mut v___y_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1136_: u8 = 0;
    let mut v___y_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_a_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1183_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v___y_1197_: u8 = 0;
    let mut v___y_1198_: u8 = 0;
    let mut v___y_1199_: u8 = 0;
    let mut v___y_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut v___y_1225_: u8 = 0;
    let mut v___y_1226_: u8 = 0;
    let mut v___y_1227_: u8 = 0;
    let mut v___y_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: u8 = 0;
    let mut v___y_1234_: u8 = 0;
    let mut v___y_1235_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1245_: u8 = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v___y_1252_: u8 = 0;
    let mut v___y_1253_: u8 = 0;
    let mut v___y_1254_: u8 = 0;
    let mut v___y_1256_: u8 = 0;
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: u8 = 0;
    let mut v___x_1263_: u8 = 0;
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: u8 = 0;
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: u8 = 0;
    let mut v___x_1269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1250_ = 2;
                v___x_1268_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1128_, v___x_1250_);
                if v___x_1268_ == 0 {
                    v___y_1256_ = v___x_1268_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1127_);
                    v___x_1269_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1127_);
                    v___y_1256_ = v___x_1269_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1142_ = l_Lean_Elab_Command_getScope___redArg(v___y_1141_);
                if crate::leanh::lean_obj_tag(v___x_1142_) == 0 {
                    v_a_1143_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                    crate::leanh::lean_inc(v_a_1143_);
                    crate::leanh::lean_dec_ref_known(v___x_1142_, 1);
                    v___x_1144_ = l_Lean_Elab_Command_getScope___redArg(v___y_1141_);
                    if crate::leanh::lean_obj_tag(v___x_1144_) == 0 {
                        v_a_1145_ = crate::leanh::lean_ctor_get(v___x_1144_, 0);
                        v_isSharedCheck_1179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1144_)) as u8;
                        if v_isSharedCheck_1179_ == 0 {
                            v___x_1147_ = v___x_1144_;
                            v_isShared_1148_ = v_isSharedCheck_1179_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1145_);
                            crate::leanh::lean_dec(v___x_1144_);
                            v___x_1147_ = crate::leanh::lean_box(0);
                            v_isShared_1148_ = v_isSharedCheck_1179_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1143_);
                        crate::leanh::lean_dec(v___y_1140_);
                        crate::leanh::lean_dec_ref(v___y_1137_);
                        crate::leanh::lean_dec_ref(v___y_1135_);
                        v_a_1180_ = crate::leanh::lean_ctor_get(v___x_1144_, 0);
                        v_isSharedCheck_1187_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1144_)) as u8;
                        if v_isSharedCheck_1187_ == 0 {
                            v___x_1182_ = v___x_1144_;
                            v_isShared_1183_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1180_);
                            crate::leanh::lean_dec(v___x_1144_);
                            v___x_1182_ = crate::leanh::lean_box(0);
                            v_isShared_1183_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1140_);
                    crate::leanh::lean_dec_ref(v___y_1137_);
                    crate::leanh::lean_dec_ref(v___y_1135_);
                    v_a_1188_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                    v_isSharedCheck_1195_ = (!crate::leanh::lean_is_exclusive(v___x_1142_)) as u8;
                    if v_isSharedCheck_1195_ == 0 {
                        v___x_1190_ = v___x_1142_;
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1188_);
                        crate::leanh::lean_dec(v___x_1142_);
                        v___x_1190_ = crate::leanh::lean_box(0);
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1149_ = lean_st_ref_take(v___y_1141_);
                v_currNamespace_1150_ = crate::leanh::lean_ctor_get(v_a_1143_, 2);
                crate::leanh::lean_inc(v_currNamespace_1150_);
                crate::leanh::lean_dec(v_a_1143_);
                v_openDecls_1151_ = crate::leanh::lean_ctor_get(v_a_1145_, 3);
                crate::leanh::lean_inc(v_openDecls_1151_);
                crate::leanh::lean_dec(v_a_1145_);
                v_env_1152_ = crate::leanh::lean_ctor_get(v___x_1149_, 0);
                v_messages_1153_ = crate::leanh::lean_ctor_get(v___x_1149_, 1);
                v_scopes_1154_ = crate::leanh::lean_ctor_get(v___x_1149_, 2);
                v_usedQuotCtxts_1155_ = crate::leanh::lean_ctor_get(v___x_1149_, 3);
                v_nextMacroScope_1156_ = crate::leanh::lean_ctor_get(v___x_1149_, 4);
                v_maxRecDepth_1157_ = crate::leanh::lean_ctor_get(v___x_1149_, 5);
                v_ngen_1158_ = crate::leanh::lean_ctor_get(v___x_1149_, 6);
                v_auxDeclNGen_1159_ = crate::leanh::lean_ctor_get(v___x_1149_, 7);
                v_infoState_1160_ = crate::leanh::lean_ctor_get(v___x_1149_, 8);
                v_traceState_1161_ = crate::leanh::lean_ctor_get(v___x_1149_, 9);
                v_snapshotTasks_1162_ = crate::leanh::lean_ctor_get(v___x_1149_, 10);
                v_isSharedCheck_1178_ = (!crate::leanh::lean_is_exclusive(v___x_1149_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v___x_1164_ = v___x_1149_;
                    v_isShared_1165_ = v_isSharedCheck_1178_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1162_);
                    crate::leanh::lean_inc(v_traceState_1161_);
                    crate::leanh::lean_inc(v_infoState_1160_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1159_);
                    crate::leanh::lean_inc(v_ngen_1158_);
                    crate::leanh::lean_inc(v_maxRecDepth_1157_);
                    crate::leanh::lean_inc(v_nextMacroScope_1156_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1155_);
                    crate::leanh::lean_inc(v_scopes_1154_);
                    crate::leanh::lean_inc(v_messages_1153_);
                    crate::leanh::lean_inc(v_env_1152_);
                    crate::leanh::lean_dec(v___x_1149_);
                    v___x_1164_ = crate::leanh::lean_box(0);
                    v_isShared_1165_ = v_isSharedCheck_1178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1166_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1166_, 0, v_currNamespace_1150_);
                crate::leanh::lean_ctor_set(v___x_1166_, 1, v_openDecls_1151_);
                v___x_1167_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1166_);
                crate::leanh::lean_ctor_set(v___x_1167_, 1, v___y_1135_);
                crate::leanh::lean_inc_ref(v___y_1138_);
                crate::leanh::lean_inc_ref(v___y_1139_);
                v___x_1168_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1168_, 0, v___y_1139_);
                crate::leanh::lean_ctor_set(v___x_1168_, 1, v___y_1137_);
                crate::leanh::lean_ctor_set(v___x_1168_, 2, v___y_1140_);
                crate::leanh::lean_ctor_set(v___x_1168_, 3, v___y_1138_);
                crate::leanh::lean_ctor_set(v___x_1168_, 4, v___x_1167_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1134_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1136_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1129_,
                );
                v___x_1169_ = l_Lean_MessageLog_add(v___x_1168_, v_messages_1153_);
                if v_isShared_1165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1164_, 1, v___x_1169_);
                    v___x_1171_ = v___x_1164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_env_1152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_scopes_1154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_usedQuotCtxts_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_nextMacroScope_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_maxRecDepth_1157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_ngen_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_auxDeclNGen_1159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_infoState_1160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_traceState_1161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 10, v_snapshotTasks_1162_);
                    v___x_1171_ = v_reuseFailAlloc_1177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1172_ = lean_st_ref_set(v___y_1141_, v___x_1171_);
                v___x_1173_ = crate::leanh::lean_box(0);
                if v_isShared_1148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1147_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1176_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1175_;
            }
            6 => {
                if v_isShared_1183_ == 0 {
                    v___x_1185_ = v___x_1182_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
                    v___x_1185_ = v_reuseFailAlloc_1186_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1185_;
            }
            8 => {
                if v_isShared_1191_ == 0 {
                    v___x_1193_ = v___x_1190_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1193_;
            }
            10 => {
                v_fileName_1202_ = crate::leanh::lean_ctor_get(v___y_1130_, 0);
                v_fileMap_1203_ = crate::leanh::lean_ctor_get(v___y_1130_, 1);
                v_suppressElabErrors_1204_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1130_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_1205_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1127_,
                    );
                v___x_1206_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_1205_, v___y_1131_);
                v_a_1207_ = crate::leanh::lean_ctor_get(v___x_1206_, 0);
                v_isSharedCheck_1223_ = (!crate::leanh::lean_is_exclusive(v___x_1206_)) as u8;
                if v_isSharedCheck_1223_ == 0 {
                    v___x_1209_ = v___x_1206_;
                    v_isShared_1210_ = v_isSharedCheck_1223_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1207_);
                    crate::leanh::lean_dec(v___x_1206_);
                    v___x_1209_ = crate::leanh::lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1223_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1203_, 2);
                v___x_1211_ = l_Lean_FileMap_toPosition(v_fileMap_1203_, v___y_1200_);
                crate::leanh::lean_dec(v___y_1200_);
                v___x_1212_ = l_Lean_FileMap_toPosition(v_fileMap_1203_, v___y_1201_);
                crate::leanh::lean_dec(v___y_1201_);
                v___x_1213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1213_, 0, v___x_1212_);
                v___x_1214_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0;
                if v_suppressElabErrors_1204_ == 0 {
                    crate::leanh::lean_del_object(v___x_1209_);
                    v___y_1134_ = v___y_1198_;
                    v___y_1135_ = v_a_1207_;
                    v___y_1136_ = v___y_1199_;
                    v___y_1137_ = v___x_1211_;
                    v___y_1138_ = v___x_1214_;
                    v___y_1139_ = v_fileName_1202_;
                    v___y_1140_ = v___x_1213_;
                    v___y_1141_ = v___y_1131_;
                    state = 1;
                    continue;
                } else {
                    v___x_1215_ = crate::leanh::lean_box((v___y_1197_) as usize);
                    v___x_1216_ = crate::leanh::lean_box((v_suppressElabErrors_1204_) as usize);
                    v___f_1217_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1217_, 0, v___x_1215_);
                    crate::leanh::lean_closure_set(v___f_1217_, 1, v___x_1216_);
                    crate::leanh::lean_inc(v_a_1207_);
                    v___x_1218_ = l_Lean_MessageData_hasTag(v___f_1217_, v_a_1207_);
                    if v___x_1218_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1213_, 1);
                        crate::leanh::lean_dec_ref(v___x_1211_);
                        crate::leanh::lean_dec(v_a_1207_);
                        v___x_1219_ = crate::leanh::lean_box(0);
                        if v_isShared_1210_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1209_, 0, v___x_1219_);
                            v___x_1221_ = v___x_1209_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1222_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
                            v___x_1221_ = v_reuseFailAlloc_1222_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1209_);
                        v___y_1134_ = v___y_1198_;
                        v___y_1135_ = v_a_1207_;
                        v___y_1136_ = v___y_1199_;
                        v___y_1137_ = v___x_1211_;
                        v___y_1138_ = v___x_1214_;
                        v___y_1139_ = v_fileName_1202_;
                        v___y_1140_ = v___x_1213_;
                        v___y_1141_ = v___y_1131_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1221_;
            }
            13 => {
                v___x_1230_ = l_Lean_Syntax_getTailPos_x3f(v___y_1228_, v___y_1226_);
                crate::leanh::lean_dec(v___y_1228_);
                if crate::leanh::lean_obj_tag(v___x_1230_) == 0 {
                    crate::leanh::lean_inc(v___y_1229_);
                    v___y_1197_ = v___y_1225_;
                    v___y_1198_ = v___y_1226_;
                    v___y_1199_ = v___y_1227_;
                    v___y_1200_ = v___y_1229_;
                    v___y_1201_ = v___y_1229_;
                    state = 10;
                    continue;
                } else {
                    v_val_1231_ = crate::leanh::lean_ctor_get(v___x_1230_, 0);
                    crate::leanh::lean_inc(v_val_1231_);
                    crate::leanh::lean_dec_ref_known(v___x_1230_, 1);
                    v___y_1197_ = v___y_1225_;
                    v___y_1198_ = v___y_1226_;
                    v___y_1199_ = v___y_1227_;
                    v___y_1200_ = v___y_1229_;
                    v___y_1201_ = v_val_1231_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1236_ = l_Lean_Elab_Command_getRef___redArg(v___y_1130_);
                if crate::leanh::lean_obj_tag(v___x_1236_) == 0 {
                    v_a_1237_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                    crate::leanh::lean_inc(v_a_1237_);
                    crate::leanh::lean_dec_ref_known(v___x_1236_, 1);
                    v_ref_1238_ = l_Lean_replaceRef(v_ref_1126_, v_a_1237_);
                    crate::leanh::lean_dec(v_a_1237_);
                    v___x_1239_ = l_Lean_Syntax_getPos_x3f(v_ref_1238_, v___y_1234_);
                    if crate::leanh::lean_obj_tag(v___x_1239_) == 0 {
                        v___x_1240_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_1225_ = v___y_1233_;
                        v___y_1226_ = v___y_1234_;
                        v___y_1227_ = v___y_1235_;
                        v___y_1228_ = v_ref_1238_;
                        v___y_1229_ = v___x_1240_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1241_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                        crate::leanh::lean_inc(v_val_1241_);
                        crate::leanh::lean_dec_ref_known(v___x_1239_, 1);
                        v___y_1225_ = v___y_1233_;
                        v___y_1226_ = v___y_1234_;
                        v___y_1227_ = v___y_1235_;
                        v___y_1228_ = v_ref_1238_;
                        v___y_1229_ = v_val_1241_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1127_);
                    v_a_1242_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                    v_isSharedCheck_1249_ = (!crate::leanh::lean_is_exclusive(v___x_1236_)) as u8;
                    if v_isSharedCheck_1249_ == 0 {
                        v___x_1244_ = v___x_1236_;
                        v_isShared_1245_ = v_isSharedCheck_1249_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1242_);
                        crate::leanh::lean_dec(v___x_1236_);
                        v___x_1244_ = crate::leanh::lean_box(0);
                        v_isShared_1245_ = v_isSharedCheck_1249_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1245_ == 0 {
                    v___x_1247_ = v___x_1244_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
                    v___x_1247_ = v_reuseFailAlloc_1248_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1247_;
            }
            17 => {
                if v___y_1254_ == 0 {
                    v___y_1233_ = v___y_1252_;
                    v___y_1234_ = v___y_1253_;
                    v___y_1235_ = v_severity_1128_;
                    state = 14;
                    continue;
                } else {
                    v___y_1233_ = v___y_1252_;
                    v___y_1234_ = v___y_1253_;
                    v___y_1235_ = v___x_1250_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1256_ == 0 {
                    v___x_1257_ = lean_st_ref_get(v___y_1131_);
                    v_scopes_1258_ = crate::leanh::lean_ctor_get(v___x_1257_, 2);
                    crate::leanh::lean_inc(v_scopes_1258_);
                    crate::leanh::lean_dec(v___x_1257_);
                    v___x_1259_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1260_ = l_List_head_x21___redArg(v___x_1259_, v_scopes_1258_);
                    crate::leanh::lean_dec(v_scopes_1258_);
                    v_opts_1261_ = crate::leanh::lean_ctor_get(v___x_1260_, 1);
                    crate::leanh::lean_inc_ref(v_opts_1261_);
                    crate::leanh::lean_dec(v___x_1260_);
                    v___x_1262_ = 1;
                    v___x_1263_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1128_, v___x_1262_);
                    if v___x_1263_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_1261_);
                        v___y_1252_ = v___y_1256_;
                        v___y_1253_ = v___y_1256_;
                        v___y_1254_ = v___x_1263_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1264_ = l_Lean_warningAsError;
                        v___x_1265_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_1261_, v___x_1264_);
                        crate::leanh::lean_dec_ref(v_opts_1261_);
                        v___y_1252_ = v___y_1256_;
                        v___y_1253_ = v___y_1256_;
                        v___y_1254_ = v___x_1265_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1127_);
                    v___x_1266_ = crate::leanh::lean_box(0);
                    v___x_1267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1266_);
                    return v___x_1267_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(
    mut v_ref_1270_: *mut crate::leanh::LeanObject,
    mut v_msgData_1271_: *mut crate::leanh::LeanObject,
    mut v_severity_1272_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1277_: u8 = 0;
    let mut v_isSilent_boxed_1278_: u8 = 0;
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1277_ = (crate::leanh::lean_unbox(v_severity_1272_) as u8);
    v_isSilent_boxed_1278_ = (crate::leanh::lean_unbox(v_isSilent_1273_) as u8);
    v_res_1279_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_1270_, v_msgData_1271_, v_severity_boxed_1277_, v_isSilent_boxed_1278_, v___y_1274_, v___y_1275_);
    crate::leanh::lean_dec(v___y_1275_);
    crate::leanh::lean_dec_ref(v___y_1274_);
    crate::leanh::lean_dec(v_ref_1270_);
    return v_res_1279_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(
    mut v_ref_1280_: *mut crate::leanh::LeanObject,
    mut v_msgData_1281_: *mut crate::leanh::LeanObject,
    mut v___y_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = 1;
    v___x_1286_ = 0;
    v___x_1287_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_1280_, v_msgData_1281_, v___x_1285_, v___x_1286_, v___y_1282_, v___y_1283_);
    return v___x_1287_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(
    mut v_ref_1288_: *mut crate::leanh::LeanObject,
    mut v_msgData_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_1288_, v_msgData_1289_, v___y_1290_, v___y_1291_);
    crate::leanh::lean_dec(v___y_1291_);
    crate::leanh::lean_dec_ref(v___y_1290_);
    crate::leanh::lean_dec(v_ref_1288_);
    return v_res_1293_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0;
    v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
    return v___x_1296_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2;
    v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
    return v___x_1299_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
    mut v_linterOption_1300_: *mut crate::leanh::LeanObject,
    mut v_stx_1301_: *mut crate::leanh::LeanObject,
    mut v_msg_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_unused_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1306_ = crate::leanh::lean_ctor_get(v_linterOption_1300_, 0);
                v_isSharedCheck_1323_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_1300_)) as u8;
                if v_isSharedCheck_1323_ == 0 {
                    v_unused_1324_ = crate::leanh::lean_ctor_get(v_linterOption_1300_, 1);
                    crate::leanh::lean_dec(v_unused_1324_);
                    v___x_1308_ = v_linterOption_1300_;
                    v_isShared_1309_ = v_isSharedCheck_1323_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1306_);
                    crate::leanh::lean_dec(v_linterOption_1300_);
                    v___x_1308_ = crate::leanh::lean_box(0);
                    v_isShared_1309_ = v_isSharedCheck_1323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
                crate::leanh::lean_inc(v_name_1306_);
                v___x_1311_ = l_Lean_MessageData_ofName(v_name_1306_);
                if v_isShared_1309_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1308_, 7);
                    crate::leanh::lean_ctor_set(v___x_1308_, 1, v___x_1311_);
                    crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1310_);
                    v___x_1313_ = v___x_1308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1311_);
                    v___x_1313_ = v_reuseFailAlloc_1322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
                v___x_1315_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1313_);
                crate::leanh::lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                v_disable_1316_ = l_Lean_MessageData_note(v___x_1315_);
                v___x_1317_ = l_Lean_Linter_linterMessageTag;
                v___x_1318_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1318_, 0, v_msg_1302_);
                crate::leanh::lean_ctor_set(v___x_1318_, 1, v_disable_1316_);
                v___x_1319_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1317_);
                crate::leanh::lean_ctor_set(v___x_1319_, 1, v___x_1318_);
                v___x_1320_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1320_, 0, v_name_1306_);
                crate::leanh::lean_ctor_set(v___x_1320_, 1, v___x_1319_);
                v___x_1321_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_1301_, v___x_1320_, v___y_1303_, v___y_1304_);
                return v___x_1321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(
    mut v_linterOption_1325_: *mut crate::leanh::LeanObject,
    mut v_stx_1326_: *mut crate::leanh::LeanObject,
    mut v_msg_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
        v_linterOption_1325_,
        v_stx_1326_,
        v_msg_1327_,
        v___y_1328_,
        v___y_1329_,
    );
    crate::leanh::lean_dec(v___y_1329_);
    crate::leanh::lean_dec_ref(v___y_1328_);
    crate::leanh::lean_dec(v_stx_1326_);
    return v_res_1331_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1;
    v___x_1336_ = l_Lean_MessageData_ofFormat(v___x_1335_);
    return v___x_1336_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(
    mut v_as_1352_: *mut crate::leanh::LeanObject,
    mut v_sz_1353_: usize,
    mut v_i_1354_: usize,
    mut v_b_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: usize = 0;
    let mut v___x_1362_: usize = 0;
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patHead_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1364_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
                if v___x_1364_ == 0 {
                    v___x_1365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1365_, 0, v_b_1355_);
                    return v___x_1365_;
                } else {
                    v___x_1366_ = crate::leanh::lean_box(0);
                    v_a_1374_ = lean_array_uget_borrowed(v_as_1352_, v_i_1354_);
                    v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4;
                    crate::leanh::lean_inc(v_a_1374_);
                    v___x_1376_ = l_Lean_Syntax_isOfKind(v_a_1374_, v___x_1375_);
                    if v___x_1376_ == 0 {
                        v_a_1360_ = v___x_1366_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1377_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1378_ = l_Lean_Syntax_getArg(v_a_1374_, v___x_1377_);
                        v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6;
                        crate::leanh::lean_inc(v___x_1378_);
                        v___x_1380_ = l_Lean_Syntax_isOfKind(v___x_1378_, v___x_1379_);
                        if v___x_1380_ == 0 {
                            v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8;
                            crate::leanh::lean_inc(v___x_1378_);
                            v___x_1382_ = l_Lean_Syntax_isOfKind(v___x_1378_, v___x_1381_);
                            if v___x_1382_ == 0 {
                                crate::leanh::lean_dec(v___x_1378_);
                                v_a_1360_ = v___x_1366_;
                                state = 1;
                                continue;
                            } else {
                                v_patHead_1368_ = v___x_1378_;
                                v___y_1369_ = v___y_1356_;
                                v___y_1370_ = v___y_1357_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1383_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1384_ = l_Lean_Syntax_getArg(v___x_1378_, v___x_1383_);
                            crate::leanh::lean_dec(v___x_1378_);
                            v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8;
                            crate::leanh::lean_inc(v___x_1384_);
                            v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
                            if v___x_1386_ == 0 {
                                crate::leanh::lean_dec(v___x_1384_);
                                v_a_1360_ = v___x_1366_;
                                state = 1;
                                continue;
                            } else {
                                v_patHead_1368_ = v___x_1384_;
                                v___y_1369_ = v___y_1356_;
                                v___y_1370_ = v___y_1357_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1361_ = 1usize;
                v___x_1362_ = lean_usize_add(v_i_1354_, v___x_1361_);
                v_i_1354_ = v___x_1362_;
                v_b_1355_ = v_a_1360_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1371_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
                v___x_1372_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
                v___x_1373_ =
                    l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
                        v___x_1371_,
                        v_patHead_1368_,
                        v___x_1372_,
                        v___y_1369_,
                        v___y_1370_,
                    );
                crate::leanh::lean_dec(v_patHead_1368_);
                if crate::leanh::lean_obj_tag(v___x_1373_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1373_, 1);
                    v_a_1360_ = v___x_1366_;
                    state = 1;
                    continue;
                } else {
                    return v___x_1373_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___boxed(
    mut v_as_1387_: *mut crate::leanh::LeanObject,
    mut v_sz_1388_: *mut crate::leanh::LeanObject,
    mut v_i_1389_: *mut crate::leanh::LeanObject,
    mut v_b_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1394_: usize = 0;
    let mut v_i_boxed_1395_: usize = 0;
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1394_ = crate::leanh::lean_unbox_usize(v_sz_1388_);
    crate::leanh::lean_dec(v_sz_1388_);
    v_i_boxed_1395_ = crate::leanh::lean_unbox_usize(v_i_1389_);
    crate::leanh::lean_dec(v_i_1389_);
    v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_1387_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1390_, v___y_1391_, v___y_1392_);
    crate::leanh::lean_dec(v___y_1392_);
    crate::leanh::lean_dec_ref(v___y_1391_);
    crate::leanh::lean_dec_ref(v_as_1387_);
    return v_res_1396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(
    mut v_sz_1403_: usize,
    mut v_i_1404_: usize,
    mut v_bs_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1406_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
                if v___x_1406_ == 0 {
                    v___x_1407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1407_, 0, v_bs_1405_);
                    return v___x_1407_;
                } else {
                    v_v_1408_ = lean_array_uget_borrowed(v_bs_1405_, v_i_1404_);
                    v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1;
                    crate::leanh::lean_inc(v_v_1408_);
                    v___x_1410_ = l_Lean_Syntax_isOfKind(v_v_1408_, v___x_1409_);
                    if v___x_1410_ == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1405_);
                        v___x_1411_ = crate::leanh::lean_box(0);
                        return v___x_1411_;
                    } else {
                        v___x_1412_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1413_ = l_Lean_Syntax_getArg(v_v_1408_, v___x_1412_);
                        crate::leanh::lean_inc(v___x_1413_);
                        v___x_1414_ = l_Lean_Syntax_matchesNull(v___x_1413_, v___x_1412_);
                        if v___x_1414_ == 0 {
                            crate::leanh::lean_dec(v___x_1413_);
                            crate::leanh::lean_dec_ref(v_bs_1405_);
                            v___x_1415_ = crate::leanh::lean_box(0);
                            return v___x_1415_;
                        } else {
                            v___x_1416_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1417_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1416_);
                            crate::leanh::lean_dec(v___x_1413_);
                            crate::leanh::lean_inc(v___x_1417_);
                            v___x_1418_ = l_Lean_Syntax_matchesNull(v___x_1417_, v___x_1412_);
                            if v___x_1418_ == 0 {
                                crate::leanh::lean_dec(v___x_1417_);
                                crate::leanh::lean_dec_ref(v_bs_1405_);
                                v___x_1419_ = crate::leanh::lean_box(0);
                                return v___x_1419_;
                            } else {
                                v_bs_x27_1420_ =
                                    lean_array_uset(v_bs_1405_, v_i_1404_, v___x_1416_);
                                v___x_1421_ = l_Lean_Syntax_getArg(v___x_1417_, v___x_1416_);
                                crate::leanh::lean_dec(v___x_1417_);
                                v___x_1422_ = 1usize;
                                v___x_1423_ = lean_usize_add(v_i_1404_, v___x_1422_);
                                v___x_1424_ =
                                    lean_array_uset(v_bs_x27_1420_, v_i_1404_, v___x_1421_);
                                v_i_1404_ = v___x_1423_;
                                v_bs_1405_ = v___x_1424_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___boxed(
    mut v_sz_1426_: *mut crate::leanh::LeanObject,
    mut v_i_1427_: *mut crate::leanh::LeanObject,
    mut v_bs_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1429_: usize = 0;
    let mut v_i_boxed_1430_: usize = 0;
    let mut v_res_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1429_ = crate::leanh::lean_unbox_usize(v_sz_1426_);
    crate::leanh::lean_dec(v_sz_1426_);
    v_i_boxed_1430_ = crate::leanh::lean_unbox_usize(v_i_1427_);
    crate::leanh::lean_dec(v_i_1427_);
    v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_1429_, v_i_boxed_1430_, v_bs_1428_);
    return v_res_1431_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(
    mut v___x_1432_: u8,
    mut v_as_1433_: *mut crate::leanh::LeanObject,
    mut v_i_1434_: usize,
    mut v_stop_1435_: usize,
    mut v_b_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v_fst_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v_snd_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_unused_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1442_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
                if v___x_1442_ == 0 {
                    v_fst_1443_ = crate::leanh::lean_ctor_get(v_b_1436_, 0);
                    v___x_1444_ = (crate::leanh::lean_unbox(v_fst_1443_) as u8);
                    if v___x_1444_ == 0 {
                        v_snd_1445_ = crate::leanh::lean_ctor_get(v_b_1436_, 1);
                        v_isSharedCheck_1453_ = (!crate::leanh::lean_is_exclusive(v_b_1436_)) as u8;
                        if v_isSharedCheck_1453_ == 0 {
                            v_unused_1454_ = crate::leanh::lean_ctor_get(v_b_1436_, 0);
                            crate::leanh::lean_dec(v_unused_1454_);
                            v___x_1447_ = v_b_1436_;
                            v_isShared_1448_ = v_isSharedCheck_1453_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1445_);
                            crate::leanh::lean_dec(v_b_1436_);
                            v___x_1447_ = crate::leanh::lean_box(0);
                            v_isShared_1448_ = v_isSharedCheck_1453_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_1455_ = crate::leanh::lean_ctor_get(v_b_1436_, 1);
                        v_isSharedCheck_1465_ = (!crate::leanh::lean_is_exclusive(v_b_1436_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = crate::leanh::lean_ctor_get(v_b_1436_, 0);
                            crate::leanh::lean_dec(v_unused_1466_);
                            v___x_1457_ = v_b_1436_;
                            v_isShared_1458_ = v_isSharedCheck_1465_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1455_);
                            crate::leanh::lean_dec(v_b_1436_);
                            v___x_1457_ = crate::leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1465_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_1436_;
                }
            }
            1 => {
                v___x_1439_ = 1usize;
                v___x_1440_ = lean_usize_add(v_i_1434_, v___x_1439_);
                v_i_1434_ = v___x_1440_;
                v_b_1436_ = v___y_1438_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1449_ = crate::leanh::lean_box((v___x_1432_) as usize);
                if v_isShared_1448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1449_);
                    v___x_1451_ = v___x_1447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_snd_1445_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1438_ = v___x_1451_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1459_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
                crate::leanh::lean_inc(v___x_1459_);
                v___x_1460_ = lean_array_push(v_snd_1455_, v___x_1459_);
                v___x_1461_ = crate::leanh::lean_box((v___x_1442_) as usize);
                if v_isShared_1458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1457_, 1, v___x_1460_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1461_);
                    v___x_1463_ = v___x_1457_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1460_);
                    v___x_1463_ = v_reuseFailAlloc_1464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1438_ = v___x_1463_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6___boxed(
    mut v___x_1467_: *mut crate::leanh::LeanObject,
    mut v_as_1468_: *mut crate::leanh::LeanObject,
    mut v_i_1469_: *mut crate::leanh::LeanObject,
    mut v_stop_1470_: *mut crate::leanh::LeanObject,
    mut v_b_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_26559__boxed_1472_: u8 = 0;
    let mut v_i_boxed_1473_: usize = 0;
    let mut v_stop_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_26559__boxed_1472_ = (crate::leanh::lean_unbox(v___x_1467_) as u8);
    v_i_boxed_1473_ = crate::leanh::lean_unbox_usize(v_i_1469_);
    crate::leanh::lean_dec(v_i_1469_);
    v_stop_boxed_1474_ = crate::leanh::lean_unbox_usize(v_stop_1470_);
    crate::leanh::lean_dec(v_stop_1470_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_26559__boxed_1472_, v_as_1468_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1471_);
    crate::leanh::lean_dec_ref(v_as_1468_);
    return v_res_1475_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(
    mut v___x_1486_: u8,
    mut v_as_1487_: *mut crate::leanh::LeanObject,
    mut v_i_1488_: usize,
    mut v_stop_1489_: usize,
) -> u8 {
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut v___y_1493_: u8 = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: usize = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1490_ = lean_usize_dec_eq(v_i_1488_, v_stop_1489_);
                if v___x_1490_ == 0 {
                    v___x_1491_ = 1;
                    v___x_1497_ = lean_array_uget_borrowed(v_as_1487_, v_i_1488_);
                    v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2;
                    crate::leanh::lean_inc(v___x_1497_);
                    v___x_1499_ = l_Lean_Syntax_isOfKind(v___x_1497_, v___x_1498_);
                    if v___x_1499_ == 0 {
                        v___y_1493_ = v___x_1499_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1500_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1501_ = l_Lean_Syntax_getArg(v___x_1497_, v___x_1500_);
                        v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4;
                        v___x_1503_ = l_Lean_Syntax_matchesIdent(v___x_1501_, v___x_1502_);
                        crate::leanh::lean_dec(v___x_1501_);
                        if v___x_1503_ == 0 {
                            v___y_1493_ = v___x_1503_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1504_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1505_ = l_Lean_Syntax_getArg(v___x_1497_, v___x_1504_);
                            v___x_1506_ = l_Lean_Syntax_matchesNull(v___x_1505_, v___x_1504_);
                            if v___x_1506_ == 0 {
                                v___y_1493_ = v___x_1506_;
                                state = 1;
                                continue;
                            } else {
                                v___y_1493_ = v___x_1486_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1507_ = 0;
                    return v___x_1507_;
                }
            }
            1 => {
                if v___y_1493_ == 0 {
                    v___x_1494_ = 1usize;
                    v___x_1495_ = lean_usize_add(v_i_1488_, v___x_1494_);
                    v_i_1488_ = v___x_1495_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1491_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___boxed(
    mut v___x_1508_: *mut crate::leanh::LeanObject,
    mut v_as_1509_: *mut crate::leanh::LeanObject,
    mut v_i_1510_: *mut crate::leanh::LeanObject,
    mut v_stop_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_26644__boxed_1512_: u8 = 0;
    let mut v_i_boxed_1513_: usize = 0;
    let mut v_stop_boxed_1514_: usize = 0;
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_26644__boxed_1512_ = (crate::leanh::lean_unbox(v___x_1508_) as u8);
    v_i_boxed_1513_ = crate::leanh::lean_unbox_usize(v_i_1510_);
    crate::leanh::lean_dec(v_i_1510_);
    v_stop_boxed_1514_ = crate::leanh::lean_unbox_usize(v_stop_1511_);
    crate::leanh::lean_dec(v_stop_1511_);
    v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_26644__boxed_1512_, v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_);
    crate::leanh::lean_dec_ref(v_as_1509_);
    v_r_1516_ = crate::leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(
    mut v_cmdStx_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___y_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1703_: usize = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1746_: usize = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v_unused_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    let mut v___x_1778_: usize = 0;
    let mut v___x_1779_: usize = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: usize = 0;
    let mut v___x_1783_: usize = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1579_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_1573_, v___y_1574_);
                v_a_1580_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                v_isSharedCheck_1799_ = (!crate::leanh::lean_is_exclusive(v___x_1579_)) as u8;
                if v_isSharedCheck_1799_ == 0 {
                    v___x_1582_ = v___x_1579_;
                    v_isShared_1583_ = v_isSharedCheck_1799_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1580_);
                    crate::leanh::lean_dec(v___x_1579_);
                    v___x_1582_ = crate::leanh::lean_box(0);
                    v_isShared_1583_ = v_isSharedCheck_1799_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1577_ = crate::leanh::lean_box(0);
                v___x_1578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1577_);
                return v___x_1578_;
            }
            2 => {
                v___x_1584_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_1580_);
                crate::leanh::lean_dec(v_a_1580_);
                if v___x_1584_ == 0 {
                    crate::leanh::lean_dec(v_cmdStx_1572_);
                    v___x_1585_ = crate::leanh::lean_box(0);
                    if v_isShared_1583_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1585_);
                        v___x_1587_ = v___x_1582_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
                        v___x_1587_ = v_reuseFailAlloc_1588_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1589_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
                    v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0;
                    v___x_1591_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2;
                    crate::leanh::lean_inc(v_cmdStx_1572_);
                    v___x_1592_ = l_Lean_Syntax_isOfKind(v_cmdStx_1572_, v___x_1591_);
                    if v___x_1592_ == 0 {
                        crate::leanh::lean_dec(v_cmdStx_1572_);
                        v___x_1593_ = crate::leanh::lean_box(0);
                        if v_isShared_1583_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1593_);
                            v___x_1595_ = v___x_1582_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1596_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
                            v___x_1595_ = v_reuseFailAlloc_1596_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1597_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1598_ = l_Lean_Syntax_getArg(v_cmdStx_1572_, v___x_1597_);
                        v___x_1599_ =
                            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4;
                        crate::leanh::lean_inc(v___x_1598_);
                        v___x_1600_ = l_Lean_Syntax_isOfKind(v___x_1598_, v___x_1599_);
                        if v___x_1600_ == 0 {
                            crate::leanh::lean_dec(v___x_1598_);
                            crate::leanh::lean_del_object(v___x_1582_);
                            crate::leanh::lean_dec(v_cmdStx_1572_);
                            v___x_1786_ = crate::leanh::lean_box(0);
                            v___x_1787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
                            return v___x_1787_;
                        } else {
                            v___x_1788_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1597_);
                            v___x_1789_ = l_Lean_Syntax_isNone(v___x_1788_);
                            if v___x_1789_ == 0 {
                                v___x_1790_ = crate::leanh::lean_unsigned_to_nat(1);
                                crate::leanh::lean_inc(v___x_1788_);
                                v___x_1791_ = l_Lean_Syntax_matchesNull(v___x_1788_, v___x_1790_);
                                if v___x_1791_ == 0 {
                                    crate::leanh::lean_dec(v___x_1788_);
                                    crate::leanh::lean_dec(v___x_1598_);
                                    crate::leanh::lean_del_object(v___x_1582_);
                                    crate::leanh::lean_dec(v_cmdStx_1572_);
                                    v___x_1792_ = crate::leanh::lean_box(0);
                                    v___x_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                                    return v___x_1793_;
                                } else {
                                    v___x_1794_ = l_Lean_Syntax_getArg(v___x_1788_, v___x_1597_);
                                    crate::leanh::lean_dec(v___x_1788_);
                                    v___x_1795_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21;
                                    v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
                                    if v___x_1796_ == 0 {
                                        crate::leanh::lean_dec(v___x_1598_);
                                        crate::leanh::lean_del_object(v___x_1582_);
                                        crate::leanh::lean_dec(v_cmdStx_1572_);
                                        v___x_1797_ = crate::leanh::lean_box(0);
                                        v___x_1798_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1798_, 0, v___x_1797_);
                                        return v___x_1798_;
                                    } else {
                                        v___y_1757_ = v___y_1573_;
                                        v___y_1758_ = v___y_1574_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1788_);
                                v___y_1757_ = v___y_1573_;
                                v___y_1758_ = v___y_1574_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_1587_;
            }
            4 => {
                return v___x_1595_;
            }
            5 => {
                v_sz_1607_ = lean_array_size(v___y_1606_);
                v___x_1608_ = 0usize;
                v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_1607_, v___x_1608_, v___y_1606_);
                if crate::leanh::lean_obj_tag(v___x_1609_) == 0 {
                    crate::leanh::lean_dec(v___x_1598_);
                    crate::leanh::lean_dec(v_cmdStx_1572_);
                    v___x_1610_ = crate::leanh::lean_box(0);
                    if v_isShared_1583_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1582_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_val_1614_ = crate::leanh::lean_ctor_get(v___x_1609_, 0);
                    crate::leanh::lean_inc(v_val_1614_);
                    crate::leanh::lean_dec_ref_known(v___x_1609_, 1);
                    v___x_1615_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1616_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1615_);
                    v___x_1617_ = l_Lean_Syntax_matchesNull(v___x_1616_, v___x_1597_);
                    if v___x_1617_ == 0 {
                        crate::leanh::lean_dec(v_val_1614_);
                        crate::leanh::lean_dec(v___x_1598_);
                        crate::leanh::lean_dec(v_cmdStx_1572_);
                        v___x_1618_ = crate::leanh::lean_box(0);
                        if v_isShared_1583_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1618_);
                            v___x_1620_ = v___x_1582_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1621_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
                            v___x_1620_ = v_reuseFailAlloc_1621_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_1622_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_1623_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1622_);
                        v___x_1624_ = l_Lean_Syntax_matchesNull(v___x_1623_, v___x_1597_);
                        if v___x_1624_ == 0 {
                            crate::leanh::lean_dec(v_val_1614_);
                            crate::leanh::lean_dec(v___x_1598_);
                            crate::leanh::lean_dec(v_cmdStx_1572_);
                            v___x_1625_ = crate::leanh::lean_box(0);
                            if v_isShared_1583_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1625_);
                                v___x_1627_ = v___x_1582_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1628_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
                                v___x_1627_ = v_reuseFailAlloc_1628_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_1629_ = crate::leanh::lean_unsigned_to_nat(5);
                            v___x_1630_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1629_);
                            v___x_1631_ = l_Lean_Syntax_matchesNull(v___x_1630_, v___x_1597_);
                            if v___x_1631_ == 0 {
                                crate::leanh::lean_dec(v_val_1614_);
                                crate::leanh::lean_dec(v___x_1598_);
                                crate::leanh::lean_dec(v_cmdStx_1572_);
                                v___x_1632_ = crate::leanh::lean_box(0);
                                if v_isShared_1583_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1632_);
                                    v___x_1634_ = v___x_1582_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1635_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1635_,
                                        0,
                                        v___x_1632_,
                                    );
                                    v___x_1634_ = v_reuseFailAlloc_1635_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v___x_1636_ = crate::leanh::lean_unsigned_to_nat(6);
                                v___x_1637_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1636_);
                                crate::leanh::lean_dec(v___x_1598_);
                                v___x_1638_ = l_Lean_Syntax_matchesNull(v___x_1637_, v___x_1597_);
                                if v___x_1638_ == 0 {
                                    crate::leanh::lean_dec(v_val_1614_);
                                    crate::leanh::lean_dec(v_cmdStx_1572_);
                                    v___x_1639_ = crate::leanh::lean_box(0);
                                    if v_isShared_1583_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1639_);
                                        v___x_1641_ = v___x_1582_;
                                        state = 10;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1642_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1642_,
                                            0,
                                            v___x_1639_,
                                        );
                                        v___x_1641_ = v_reuseFailAlloc_1642_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    v___x_1643_ = l_Lean_Syntax_getArg(v_cmdStx_1572_, v___y_1605_);
                                    crate::leanh::lean_dec(v_cmdStx_1572_);
                                    v___x_1644_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6;
                                    crate::leanh::lean_inc(v___x_1643_);
                                    v___x_1645_ = l_Lean_Syntax_isOfKind(v___x_1643_, v___x_1644_);
                                    if v___x_1645_ == 0 {
                                        crate::leanh::lean_dec(v___x_1643_);
                                        crate::leanh::lean_dec(v_val_1614_);
                                        v___x_1646_ = crate::leanh::lean_box(0);
                                        if v_isShared_1583_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_1582_,
                                                0,
                                                v___x_1646_,
                                            );
                                            v___x_1648_ = v___x_1582_;
                                            state = 11;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1649_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1649_,
                                                0,
                                                v___x_1646_,
                                            );
                                            v___x_1648_ = v_reuseFailAlloc_1649_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v___x_1650_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_1651_ =
                                            l_Lean_Syntax_getArg(v___x_1643_, v___x_1650_);
                                        v___x_1652_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8;
                                        crate::leanh::lean_inc(v___x_1651_);
                                        v___x_1653_ =
                                            l_Lean_Syntax_isOfKind(v___x_1651_, v___x_1652_);
                                        if v___x_1653_ == 0 {
                                            crate::leanh::lean_dec(v___x_1651_);
                                            crate::leanh::lean_dec(v___x_1643_);
                                            crate::leanh::lean_dec(v_val_1614_);
                                            v___x_1654_ = crate::leanh::lean_box(0);
                                            if v_isShared_1583_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_1582_,
                                                    0,
                                                    v___x_1654_,
                                                );
                                                v___x_1656_ = v___x_1582_;
                                                state = 12;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_1657_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_1657_,
                                                    0,
                                                    v___x_1654_,
                                                );
                                                v___x_1656_ = v_reuseFailAlloc_1657_;
                                                state = 12;
                                                continue;
                                            }
                                        } else {
                                            v___x_1658_ =
                                                l_Lean_Syntax_getArg(v___x_1651_, v___x_1597_);
                                            v___x_1659_ =
                                                l_Lean_Syntax_matchesNull(v___x_1658_, v___x_1597_);
                                            if v___x_1659_ == 0 {
                                                crate::leanh::lean_dec(v___x_1651_);
                                                crate::leanh::lean_dec(v___x_1643_);
                                                crate::leanh::lean_dec(v_val_1614_);
                                                v___x_1660_ = crate::leanh::lean_box(0);
                                                if v_isShared_1583_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_1582_,
                                                        0,
                                                        v___x_1660_,
                                                    );
                                                    v___x_1662_ = v___x_1582_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_1663_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_1663_,
                                                        0,
                                                        v___x_1660_,
                                                    );
                                                    v___x_1662_ = v_reuseFailAlloc_1663_;
                                                    state = 13;
                                                    continue;
                                                }
                                            } else {
                                                v___x_1664_ =
                                                    l_Lean_Syntax_getArg(v___x_1651_, v___y_1605_);
                                                crate::leanh::lean_dec(v___x_1651_);
                                                crate::leanh::lean_inc(v___x_1664_);
                                                v___x_1665_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1664_,
                                                    v___y_1605_,
                                                );
                                                if v___x_1665_ == 0 {
                                                    crate::leanh::lean_dec(v___x_1664_);
                                                    crate::leanh::lean_dec(v___x_1643_);
                                                    crate::leanh::lean_dec(v_val_1614_);
                                                    v___x_1666_ = crate::leanh::lean_box(0);
                                                    if v_isShared_1583_ == 0 {
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_1582_,
                                                            0,
                                                            v___x_1666_,
                                                        );
                                                        v___x_1668_ = v___x_1582_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_1669_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                0,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_1669_,
                                                            0,
                                                            v___x_1666_,
                                                        );
                                                        v___x_1668_ = v_reuseFailAlloc_1669_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_1670_ = l_Lean_Syntax_getArg(
                                                        v___x_1664_,
                                                        v___x_1597_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_1664_);
                                                    v___x_1671_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9;
                                                    crate::leanh::lean_inc_ref(v___y_1602_);
                                                    v___x_1672_ = l_Lean_Name_mkStr4(
                                                        v___x_1589_,
                                                        v___x_1590_,
                                                        v___y_1602_,
                                                        v___x_1671_,
                                                    );
                                                    v___x_1673_ = l_Lean_Syntax_isOfKind(
                                                        v___x_1670_,
                                                        v___x_1672_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_1672_);
                                                    if v___x_1673_ == 0 {
                                                        crate::leanh::lean_dec(v___x_1643_);
                                                        crate::leanh::lean_dec(v_val_1614_);
                                                        v___x_1674_ = crate::leanh::lean_box(0);
                                                        if v_isShared_1583_ == 0 {
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_1582_,
                                                                0,
                                                                v___x_1674_,
                                                            );
                                                            v___x_1676_ = v___x_1582_;
                                                            state = 15;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_1677_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_1677_,
                                                                0,
                                                                v___x_1674_,
                                                            );
                                                            v___x_1676_ = v_reuseFailAlloc_1677_;
                                                            state = 15;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___x_1678_ = l_Lean_Syntax_getArg(
                                                            v___x_1643_,
                                                            v___x_1615_,
                                                        );
                                                        v___x_1679_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11;
                                                        crate::leanh::lean_inc(v___x_1678_);
                                                        v___x_1680_ = l_Lean_Syntax_isOfKind(
                                                            v___x_1678_,
                                                            v___x_1679_,
                                                        );
                                                        if v___x_1680_ == 0 {
                                                            crate::leanh::lean_dec(v___x_1678_);
                                                            crate::leanh::lean_dec(v___x_1643_);
                                                            crate::leanh::lean_dec(v_val_1614_);
                                                            v___x_1681_ = crate::leanh::lean_box(0);
                                                            if v_isShared_1583_ == 0 {
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_1582_,
                                                                    0,
                                                                    v___x_1681_,
                                                                );
                                                                v___x_1683_ = v___x_1582_;
                                                                state = 16;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_1684_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v_reuseFailAlloc_1684_,
                                                                    0,
                                                                    v___x_1681_,
                                                                );
                                                                v___x_1683_ =
                                                                    v_reuseFailAlloc_1684_;
                                                                state = 16;
                                                                continue;
                                                            }
                                                        } else {
                                                            v___x_1685_ = l_Lean_Syntax_getArg(
                                                                v___x_1678_,
                                                                v___x_1597_,
                                                            );
                                                            crate::leanh::lean_dec(v___x_1678_);
                                                            v___x_1686_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12;
                                                            crate::leanh::lean_inc_ref(v___y_1602_);
                                                            v___x_1687_ = l_Lean_Name_mkStr4(
                                                                v___x_1589_,
                                                                v___x_1590_,
                                                                v___y_1602_,
                                                                v___x_1686_,
                                                            );
                                                            crate::leanh::lean_inc(v___x_1685_);
                                                            v___x_1688_ = l_Lean_Syntax_isOfKind(
                                                                v___x_1685_,
                                                                v___x_1687_,
                                                            );
                                                            crate::leanh::lean_dec(v___x_1687_);
                                                            if v___x_1688_ == 0 {
                                                                crate::leanh::lean_dec(v___x_1685_);
                                                                crate::leanh::lean_dec(v___x_1643_);
                                                                crate::leanh::lean_dec(v_val_1614_);
                                                                v___x_1689_ =
                                                                    crate::leanh::lean_box(0);
                                                                if v_isShared_1583_ == 0 {
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1582_,
                                                                        0,
                                                                        v___x_1689_,
                                                                    );
                                                                    v___x_1691_ = v___x_1582_;
                                                                    state = 17;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_1692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v_reuseFailAlloc_1692_,
                                                                        0,
                                                                        v___x_1689_,
                                                                    );
                                                                    v___x_1691_ =
                                                                        v_reuseFailAlloc_1692_;
                                                                    state = 17;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v___x_1693_ = l_Lean_Syntax_getArg(
                                                                    v___x_1685_,
                                                                    v___x_1597_,
                                                                );
                                                                v___x_1694_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13;
                                                                crate::leanh::lean_inc_ref(
                                                                    v___y_1602_,
                                                                );
                                                                v___x_1695_ = l_Lean_Name_mkStr4(
                                                                    v___x_1589_,
                                                                    v___x_1590_,
                                                                    v___y_1602_,
                                                                    v___x_1694_,
                                                                );
                                                                crate::leanh::lean_inc(v___x_1693_);
                                                                v___x_1696_ =
                                                                    l_Lean_Syntax_isOfKind(
                                                                        v___x_1693_,
                                                                        v___x_1695_,
                                                                    );
                                                                crate::leanh::lean_dec(v___x_1695_);
                                                                if v___x_1696_ == 0 {
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1693_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1685_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1643_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_val_1614_,
                                                                    );
                                                                    v___x_1697_ =
                                                                        crate::leanh::lean_box(0);
                                                                    if v_isShared_1583_ == 0 {
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_1582_,
                                                                            0,
                                                                            v___x_1697_,
                                                                        );
                                                                        v___x_1699_ = v___x_1582_;
                                                                        state = 18;
                                                                        continue;
                                                                    } else {
                                                                        v_reuseFailAlloc_1700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v_reuseFailAlloc_1700_,
                                                                            0,
                                                                            v___x_1697_,
                                                                        );
                                                                        v___x_1699_ =
                                                                            v_reuseFailAlloc_1700_;
                                                                        state = 18;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    v___x_1701_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v___x_1693_,
                                                                            v___x_1597_,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1693_,
                                                                    );
                                                                    v___x_1702_ =
                                                                        l_Lean_Syntax_getArgs(
                                                                            v___x_1701_,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1701_,
                                                                    );
                                                                    v_sz_1703_ = lean_array_size(
                                                                        v___x_1702_,
                                                                    );
                                                                    v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_1703_, v___x_1608_, v___x_1702_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_1704_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1685_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1643_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_val_1614_,
                                                                        );
                                                                        v___x_1705_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        if v_isShared_1583_ == 0 {
                                                                            crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1705_);
                                                                            v___x_1707_ =
                                                                                v___x_1582_;
                                                                            state = 19;
                                                                            continue;
                                                                        } else {
                                                                            v_reuseFailAlloc_1708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
                                                                            v___x_1707_ = v_reuseFailAlloc_1708_;
                                                                            state = 19;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_val_1709_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_val_1709_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_1704_, 1);
                                                                        v___x_1710_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v___x_1685_,
                                                                                v___y_1605_,
                                                                            );
                                                                        v___x_1711_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16;
                                                                        crate::leanh::lean_inc(
                                                                            v___x_1710_,
                                                                        );
                                                                        v___x_1712_ =
                                                                            l_Lean_Syntax_isOfKind(
                                                                                v___x_1710_,
                                                                                v___x_1711_,
                                                                            );
                                                                        if v___x_1712_ == 0 {
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1710_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v_val_1709_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1685_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1643_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v_val_1614_,
                                                                            );
                                                                            v___x_1713_ = crate::leanh::lean_box(0);
                                                                            if v_isShared_1583_ == 0
                                                                            {
                                                                                crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1713_);
                                                                                v___x_1715_ =
                                                                                    v___x_1582_;
                                                                                state = 20;
                                                                                continue;
                                                                            } else {
                                                                                v_reuseFailAlloc_1716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
                                                                                v___x_1715_ = v_reuseFailAlloc_1716_;
                                                                                state = 20;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            v___x_1717_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1597_);
                                                                            v___x_1718_ = l_Lean_Syntax_matchesNull(v___x_1717_, v___x_1597_);
                                                                            if v___x_1718_ == 0 {
                                                                                crate::leanh::lean_dec(v___x_1710_);
                                                                                crate::leanh::lean_dec(v_val_1709_);
                                                                                crate::leanh::lean_dec(v___x_1685_);
                                                                                crate::leanh::lean_dec(v___x_1643_);
                                                                                crate::leanh::lean_dec(v_val_1614_);
                                                                                v___x_1719_ = crate::leanh::lean_box(0);
                                                                                if v_isShared_1583_
                                                                                    == 0
                                                                                {
                                                                                    crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1719_);
                                                                                    v___x_1721_ =
                                                                                        v___x_1582_;
                                                                                    state = 21;
                                                                                    continue;
                                                                                } else {
                                                                                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                                                                                    v___x_1721_ = v_reuseFailAlloc_1722_;
                                                                                    state = 21;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                v___x_1723_ = l_Lean_Syntax_getArg(v___x_1710_, v___y_1605_);
                                                                                crate::leanh::lean_dec(v___x_1710_);
                                                                                v___x_1724_ = l_Lean_Syntax_matchesNull(v___x_1723_, v___x_1597_);
                                                                                if v___x_1724_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec(v_val_1709_);
                                                                                    crate::leanh::lean_dec(v___x_1685_);
                                                                                    crate::leanh::lean_dec(v___x_1643_);
                                                                                    crate::leanh::lean_dec(v_val_1614_);
                                                                                    v___x_1725_ = crate::leanh::lean_box(0);
                                                                                    if v_isShared_1583_ == 0 {
crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1725_);
v___x_1727_ = v___x_1582_;
state = 22; continue;
} else {
v_reuseFailAlloc_1728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
state = 22; continue;
}
                                                                                } else {
                                                                                    v___x_1729_ = l_Lean_Syntax_getArg(v___x_1685_, v___x_1650_);
                                                                                    crate::leanh::lean_dec(v___x_1685_);
                                                                                    v___x_1730_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1597_);
                                                                                    if v___x_1730_
                                                                                        == 0
                                                                                    {
                                                                                        crate::leanh::lean_dec(v_val_1709_);
                                                                                        crate::leanh::lean_dec(v___x_1643_);
                                                                                        crate::leanh::lean_dec(v_val_1614_);
                                                                                        v___x_1731_ = crate::leanh::lean_box(0);
                                                                                        if v_isShared_1583_ == 0 {
crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1731_);
v___x_1733_ = v___x_1582_;
state = 23; continue;
} else {
v_reuseFailAlloc_1734_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
crate::leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
state = 23; continue;
}
                                                                                    } else {
                                                                                        v___x_1735_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1622_);
                                                                                        crate::leanh::lean_dec(v___x_1643_);
                                                                                        v___x_1736_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___x_1597_);
                                                                                        if v___x_1736_ == 0 {
crate::leanh::lean_dec(v_val_1709_);
crate::leanh::lean_dec(v_val_1614_);
v___x_1737_ = crate::leanh::lean_box(0);
if v_isShared_1583_ == 0 {
crate::leanh::lean_ctor_set(v___x_1582_, 0, v___x_1737_);
v___x_1739_ = v___x_1582_;
state = 24; continue;
} else {
v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
state = 24; continue;
}
} else {
crate::leanh::lean_del_object(v___x_1582_);
v___x_1741_ = lean_array_get_size(v_val_1614_);
v___x_1742_ = lean_nat_dec_lt(v___x_1597_, v___x_1741_);
if v___x_1742_ == 0 {
crate::leanh::lean_dec(v_val_1709_);
crate::leanh::lean_dec(v_val_1614_);
state = 1; continue;
} else {
if v___x_1742_ == 0 {
crate::leanh::lean_dec(v_val_1709_);
crate::leanh::lean_dec(v_val_1614_);
state = 1; continue;
} else {
v___x_1743_ = lean_usize_of_nat(v___x_1741_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_1600_, v_val_1614_, v___x_1608_, v___x_1743_);
crate::leanh::lean_dec(v_val_1614_);
if v___x_1744_ == 0 {
crate::leanh::lean_dec(v_val_1709_);
state = 1; continue;
} else {
v___x_1745_ = crate::leanh::lean_box(0);
v_sz_1746_ = lean_array_size(v_val_1709_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_1709_, v_sz_1746_, v___x_1608_, v___x_1745_, v___y_1603_, v___y_1604_);
crate::leanh::lean_dec(v_val_1709_);
if crate::leanh::lean_obj_tag(v___x_1747_) == 0 {
v_isSharedCheck_1754_ = (!crate::leanh::lean_is_exclusive(v___x_1747_)) as u8;
if v_isSharedCheck_1754_ == 0 {
v_unused_1755_ = crate::leanh::lean_ctor_get(v___x_1747_, 0);
crate::leanh::lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1747_;
v_isShared_1750_ = v_isSharedCheck_1754_;
state = 25; continue;
} else {
crate::leanh::lean_dec(v___x_1747_);
v___x_1749_ = crate::leanh::lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
state = 25; continue;
}
} else {
return v___x_1747_;
}
}
}
}
}
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                return v___x_1612_;
            }
            7 => {
                return v___x_1620_;
            }
            8 => {
                return v___x_1627_;
            }
            9 => {
                return v___x_1634_;
            }
            10 => {
                return v___x_1641_;
            }
            11 => {
                return v___x_1648_;
            }
            12 => {
                return v___x_1656_;
            }
            13 => {
                return v___x_1662_;
            }
            14 => {
                return v___x_1668_;
            }
            15 => {
                return v___x_1676_;
            }
            16 => {
                return v___x_1683_;
            }
            17 => {
                return v___x_1691_;
            }
            18 => {
                return v___x_1699_;
            }
            19 => {
                return v___x_1707_;
            }
            20 => {
                return v___x_1715_;
            }
            21 => {
                return v___x_1721_;
            }
            22 => {
                return v___x_1727_;
            }
            23 => {
                return v___x_1733_;
            }
            24 => {
                return v___x_1739_;
            }
            25 => {
                if v_isShared_1750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1745_);
                    v___x_1752_ = v___x_1749_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1745_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1752_;
            }
            27 => {
                v___x_1759_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1760_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1759_);
                crate::leanh::lean_inc(v___x_1760_);
                v___x_1761_ = l_Lean_Syntax_matchesNull(v___x_1760_, v___x_1759_);
                if v___x_1761_ == 0 {
                    crate::leanh::lean_dec(v___x_1760_);
                    crate::leanh::lean_dec(v___x_1598_);
                    crate::leanh::lean_del_object(v___x_1582_);
                    crate::leanh::lean_dec(v_cmdStx_1572_);
                    v___x_1762_ = crate::leanh::lean_box(0);
                    v___x_1763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                } else {
                    v___x_1764_ = l_Lean_Syntax_getArg(v___x_1760_, v___x_1597_);
                    crate::leanh::lean_dec(v___x_1760_);
                    v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1;
                    v___x_1766_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18;
                    crate::leanh::lean_inc(v___x_1764_);
                    v___x_1767_ = l_Lean_Syntax_isOfKind(v___x_1764_, v___x_1766_);
                    if v___x_1767_ == 0 {
                        crate::leanh::lean_dec(v___x_1764_);
                        crate::leanh::lean_dec(v___x_1598_);
                        crate::leanh::lean_del_object(v___x_1582_);
                        crate::leanh::lean_dec(v_cmdStx_1572_);
                        v___x_1768_ = crate::leanh::lean_box(0);
                        v___x_1769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                        return v___x_1769_;
                    } else {
                        v___x_1770_ = l_Lean_Syntax_getArg(v___x_1764_, v___x_1759_);
                        crate::leanh::lean_dec(v___x_1764_);
                        v___x_1771_ = l_Lean_Syntax_getArgs(v___x_1770_);
                        crate::leanh::lean_dec(v___x_1770_);
                        v___x_1772_ =
                            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19;
                        v___x_1773_ = lean_array_get_size(v___x_1771_);
                        v___x_1774_ = lean_nat_dec_lt(v___x_1597_, v___x_1773_);
                        if v___x_1774_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1771_);
                            v___y_1602_ = v___x_1765_;
                            v___y_1603_ = v___y_1757_;
                            v___y_1604_ = v___y_1758_;
                            v___y_1605_ = v___x_1759_;
                            v___y_1606_ = v___x_1772_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1775_ = crate::leanh::lean_box((v___x_1767_) as usize);
                            v___x_1776_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
                            crate::leanh::lean_ctor_set(v___x_1776_, 1, v___x_1772_);
                            v___x_1777_ = lean_nat_dec_le(v___x_1773_, v___x_1773_);
                            if v___x_1777_ == 0 {
                                if v___x_1774_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1776_, 2);
                                    crate::leanh::lean_dec_ref(v___x_1771_);
                                    v___y_1602_ = v___x_1765_;
                                    v___y_1603_ = v___y_1757_;
                                    v___y_1604_ = v___y_1758_;
                                    v___y_1605_ = v___x_1759_;
                                    v___y_1606_ = v___x_1772_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_1778_ = 0usize;
                                    v___x_1779_ = lean_usize_of_nat(v___x_1773_);
                                    v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_1767_, v___x_1771_, v___x_1778_, v___x_1779_, v___x_1776_);
                                    crate::leanh::lean_dec_ref(v___x_1771_);
                                    v_snd_1781_ = crate::leanh::lean_ctor_get(v___x_1780_, 1);
                                    crate::leanh::lean_inc(v_snd_1781_);
                                    crate::leanh::lean_dec_ref(v___x_1780_);
                                    v___y_1602_ = v___x_1765_;
                                    v___y_1603_ = v___y_1757_;
                                    v___y_1604_ = v___y_1758_;
                                    v___y_1605_ = v___x_1759_;
                                    v___y_1606_ = v_snd_1781_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___x_1782_ = 0usize;
                                v___x_1783_ = lean_usize_of_nat(v___x_1773_);
                                v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_1767_, v___x_1771_, v___x_1782_, v___x_1783_, v___x_1776_);
                                crate::leanh::lean_dec_ref(v___x_1771_);
                                v_snd_1785_ = crate::leanh::lean_ctor_get(v___x_1784_, 1);
                                crate::leanh::lean_inc(v_snd_1785_);
                                crate::leanh::lean_dec_ref(v___x_1784_);
                                v___y_1602_ = v___x_1765_;
                                v___y_1603_ = v___y_1757_;
                                v___y_1604_ = v___y_1758_;
                                v___y_1605_ = v___x_1759_;
                                v___y_1606_ = v_snd_1785_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed(
    mut v_cmdStx_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(
        v_cmdStx_1800_,
        v___y_1801_,
        v___y_1802_,
    );
    crate::leanh::lean_dec(v___y_1802_);
    crate::leanh::lean_dec_ref(v___y_1801_);
    return v_res_1804_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(
    mut v_o_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_1814_, v___y_1816_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(
    mut v_o_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_1819_, v___y_1820_, v___y_1821_);
    crate::leanh::lean_dec(v___y_1821_);
    crate::leanh::lean_dec_ref(v___y_1820_);
    return v_res_1823_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(
    mut v_msgData_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_1824_, v___y_1826_);
    return v___x_1828_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(
    mut v_msgData_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_1829_, v___y_1830_, v___y_1831_);
    crate::leanh::lean_dec(v___y_1831_);
    crate::leanh::lean_dec_ref(v___y_1830_);
    return v_res_1833_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_Linter_suspiciousUnexpanderPatterns;
    v___x_1836_ = l_Lean_Elab_Command_addLinter(v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(
    mut v_a_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
    return v_res_1838_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Builtin(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_suspiciousUnexpanderPatterns = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_suspiciousUnexpanderPatterns);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Builtin(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Builtin(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Builtin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Builtin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Builtin(builtin);
}
