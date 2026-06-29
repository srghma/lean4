// Lean compiler output
// Module: Lean.Linter.GlobalAttributeIn
// Imports: Lean.Elab.Command Lean.Linter.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_TSepArray_getElems___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_isQuot;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 114, 97, 115, 101, 65, 116, 116, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject,14059049201606366202 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject,7499624980761693169 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value) as *mut crate::leanh::LeanObject,312453245906544776 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value) as *mut crate::leanh::LeanObject,10992023688825480391 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 110, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value) as *mut crate::leanh::LeanObject,745669085263777601 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value) as *mut crate::leanh::LeanObject,11509420844586769999 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [68, 101, 115, 112, 105, 116, 101, 32, 116, 104, 101, 32, 96, 105, 110, 96, 44, 32, 116, 104, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [32, 105, 115, 32, 97, 100, 100, 101, 100, 32, 103, 108, 111, 98, 97, 108, 108, 121, 32, 116, 111, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [10, 112, 108, 101, 97, 115, 101, 32, 114, 101, 109, 111, 118, 101, 32, 116, 104, 101, 32, 96, 105, 110, 96, 32, 111, 114, 32, 109, 97, 107, 101, 32, 116, 104, 105, 115, 32, 97, 32, 96, 108, 111, 99, 97, 108, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value) as *mut crate::leanh::LeanObject,4424989899264441540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [71, 108, 111, 98, 97, 108, 65, 116, 116, 114, 105, 98, 117, 116, 101, 73, 110, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value) as *mut crate::leanh::LeanObject,5876246626864928257 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,17296797802271896868 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,2673470441817919109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value) as *mut crate::leanh::LeanObject,16352459736160742727 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 108, 111, 98, 97, 108, 65, 116, 116, 114, 105, 98, 117, 116, 101, 73, 110, 0]};
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value) as *mut crate::leanh::LeanObject,18065664021204650726 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot(
    mut v_stx_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_stx_735_);
    return v_stx_735_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot___boxed(
    mut v_stx_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ =
        l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot(v_stx_736_);
    crate::leanh::lean_dec(v_stx_736_);
    return v_res_737_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__0(
    mut v_toApplicative_738_: *mut crate::leanh::LeanObject,
    mut v_____r_739_: *mut crate::leanh::LeanObject,
    mut v_b_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_741_ = crate::leanh::lean_ctor_get(v_toApplicative_738_, 1);
    crate::leanh::lean_inc(v_toPure_741_);
    crate::leanh::lean_dec_ref(v_toApplicative_738_);
    v___x_742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_742_, 0, v_b_740_);
    v___x_743_ = crate::leanh::lean_apply_2(v_toPure_741_, crate::leanh::lean_box(0), v___x_742_);
    return v___x_743_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__1(
    mut v___f_744_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_745_: *mut crate::leanh::LeanObject,
    mut v_____s_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_747_ = crate::leanh::lean_ctor_get(v_____s_746_, 0);
    if crate::leanh::lean_obj_tag(v_fst_747_) == 0 {
        let mut v_snd_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_745_);
        v_snd_748_ = crate::leanh::lean_ctor_get(v_____s_746_, 1);
        crate::leanh::lean_inc(v_snd_748_);
        crate::leanh::lean_dec_ref(v_____s_746_);
        v___x_749_ = crate::leanh::lean_box(0);
        v___x_750_ = crate::leanh::lean_apply_2(v___f_744_, v___x_749_, v_snd_748_);
        return v___x_750_;
    } else {
        let mut v_val_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_fst_747_);
        crate::leanh::lean_dec_ref(v_____s_746_);
        crate::leanh::lean_dec(v___f_744_);
        v_val_751_ = crate::leanh::lean_ctor_get(v_fst_747_, 0);
        crate::leanh::lean_inc(v_val_751_);
        crate::leanh::lean_dec_ref_known(v_fst_747_, 1);
        v_toPure_752_ = crate::leanh::lean_ctor_get(v_toApplicative_745_, 1);
        crate::leanh::lean_inc(v_toPure_752_);
        crate::leanh::lean_dec_ref(v_toApplicative_745_);
        v___x_753_ =
            crate::leanh::lean_apply_2(v_toPure_752_, crate::leanh::lean_box(0), v_val_751_);
        return v___x_753_;
    }
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__2(
    mut v_toApplicative_754_: *mut crate::leanh::LeanObject,
    mut v_snd_755_: *mut crate::leanh::LeanObject,
    mut v___x_756_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_766_: u8 = 0;
    let mut v_toPure_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_757_) == 0 {
                    crate::leanh::lean_dec(v___x_756_);
                    v_toPure_758_ = crate::leanh::lean_ctor_get(v_toApplicative_754_, 1);
                    crate::leanh::lean_inc(v_toPure_758_);
                    crate::leanh::lean_dec_ref(v_toApplicative_754_);
                    v___x_759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_759_, 0, v_____do__lift_757_);
                    v___x_760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
                    crate::leanh::lean_ctor_set(v___x_760_, 1, v_snd_755_);
                    v___x_761_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_760_);
                    v___x_762_ = crate::leanh::lean_apply_2(
                        v_toPure_758_,
                        crate::leanh::lean_box(0),
                        v___x_761_,
                    );
                    return v___x_762_;
                } else {
                    crate::leanh::lean_dec(v_snd_755_);
                    v_a_763_ = crate::leanh::lean_ctor_get(v_____do__lift_757_, 0);
                    v_isSharedCheck_773_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_757_)) as u8;
                    if v_isSharedCheck_773_ == 0 {
                        v___x_765_ = v_____do__lift_757_;
                        v_isShared_766_ = v_isSharedCheck_773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_763_);
                        crate::leanh::lean_dec(v_____do__lift_757_);
                        v___x_765_ = crate::leanh::lean_box(0);
                        v_isShared_766_ = v_isSharedCheck_773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toPure_767_ = crate::leanh::lean_ctor_get(v_toApplicative_754_, 1);
                crate::leanh::lean_inc(v_toPure_767_);
                crate::leanh::lean_dec_ref(v_toApplicative_754_);
                v___x_768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_756_);
                crate::leanh::lean_ctor_set(v___x_768_, 1, v_a_763_);
                if v_isShared_766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_765_, 0, v___x_768_);
                    v___x_770_ = v___x_765_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_768_);
                    v___x_770_ = v_reuseFailAlloc_772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_771_ = crate::leanh::lean_apply_2(
                    v_toPure_767_,
                    crate::leanh::lean_box(0),
                    v___x_770_,
                );
                return v___x_771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__4(
    mut v_toApplicative_774_: *mut crate::leanh::LeanObject,
    mut v_stx_775_: *mut crate::leanh::LeanObject,
    mut v_inst_776_: *mut crate::leanh::LeanObject,
    mut v_f_777_: *mut crate::leanh::LeanObject,
    mut v_toBind_778_: *mut crate::leanh::LeanObject,
    mut v___f_779_: *mut crate::leanh::LeanObject,
    mut v___f_780_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_781_) == 0 {
        let mut v_toPure_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_780_);
        crate::leanh::lean_dec(v___f_779_);
        crate::leanh::lean_dec(v_toBind_778_);
        crate::leanh::lean_dec(v_f_777_);
        crate::leanh::lean_dec_ref(v_inst_776_);
        crate::leanh::lean_dec(v_stx_775_);
        v_toPure_782_ = crate::leanh::lean_ctor_get(v_toApplicative_774_, 1);
        crate::leanh::lean_inc(v_toPure_782_);
        crate::leanh::lean_dec_ref(v_toApplicative_774_);
        v___x_783_ = crate::leanh::lean_apply_2(
            v_toPure_782_,
            crate::leanh::lean_box(0),
            v_____do__lift_781_,
        );
        return v___x_783_;
    } else {
        if crate::leanh::lean_obj_tag(v_stx_775_) == 1 {
            let mut v_a_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_789_: usize = 0;
            let mut v___x_790_: usize = 0;
            let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_780_);
            v_a_784_ = crate::leanh::lean_ctor_get(v_____do__lift_781_, 0);
            crate::leanh::lean_inc(v_a_784_);
            crate::leanh::lean_dec_ref_known(v_____do__lift_781_, 1);
            v_args_785_ = crate::leanh::lean_ctor_get(v_stx_775_, 2);
            crate::leanh::lean_inc_ref(v_args_785_);
            crate::leanh::lean_dec_ref_known(v_stx_775_, 3);
            v___x_786_ = crate::leanh::lean_box(0);
            crate::leanh::lean_inc(v_toBind_778_);
            crate::leanh::lean_inc_ref(v_inst_776_);
            v___f_787_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__3 as *mut core::ffi::c_void, 8, 5);
            crate::leanh::lean_closure_set(v___f_787_, 0, v_toApplicative_774_);
            crate::leanh::lean_closure_set(v___f_787_, 1, v___x_786_);
            crate::leanh::lean_closure_set(v___f_787_, 2, v_inst_776_);
            crate::leanh::lean_closure_set(v___f_787_, 3, v_f_777_);
            crate::leanh::lean_closure_set(v___f_787_, 4, v_toBind_778_);
            v___x_788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_786_);
            crate::leanh::lean_ctor_set(v___x_788_, 1, v_a_784_);
            v_sz_789_ = lean_array_size(v_args_785_);
            v___x_790_ = 0usize;
            v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_776_,
                v_args_785_,
                v___f_787_,
                v_sz_789_,
                v___x_790_,
                v___x_788_,
            );
            v___x_792_ = crate::leanh::lean_apply_4(
                v_toBind_778_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_791_,
                v___f_779_,
            );
            return v___x_792_;
        } else {
            let mut v_a_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___f_779_);
            crate::leanh::lean_dec(v_toBind_778_);
            crate::leanh::lean_dec(v_f_777_);
            crate::leanh::lean_dec_ref(v_inst_776_);
            crate::leanh::lean_dec(v_stx_775_);
            crate::leanh::lean_dec_ref(v_toApplicative_774_);
            v_a_793_ = crate::leanh::lean_ctor_get(v_____do__lift_781_, 0);
            crate::leanh::lean_inc(v_a_793_);
            crate::leanh::lean_dec_ref_known(v_____do__lift_781_, 1);
            v___x_794_ = crate::leanh::lean_box(0);
            v___x_795_ = crate::leanh::lean_apply_2(v___f_780_, v___x_794_, v_a_793_);
            return v___x_795_;
        }
    }
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(
    mut v_inst_796_: *mut crate::leanh::LeanObject,
    mut v_f_797_: *mut crate::leanh::LeanObject,
    mut v_stx_798_: *mut crate::leanh::LeanObject,
    mut v_b_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_800_: u8 = 0;
    v___x_800_ = l_Lean_Syntax_isQuot(v_stx_798_);
    if v___x_800_ == 0 {
        let mut v_toApplicative_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_801_ = crate::leanh::lean_ctor_get(v_inst_796_, 0);
        crate::leanh::lean_inc_ref_n(v_toApplicative_801_, 3);
        v_toBind_802_ = crate::leanh::lean_ctor_get(v_inst_796_, 1);
        crate::leanh::lean_inc_n(v_toBind_802_, 2);
        v___f_803_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
        crate::leanh::lean_closure_set(v___f_803_, 0, v_toApplicative_801_);
        crate::leanh::lean_inc_ref(v___f_803_);
        v___f_804_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_804_, 0, v___f_803_);
        crate::leanh::lean_closure_set(v___f_804_, 1, v_toApplicative_801_);
        crate::leanh::lean_inc(v_f_797_);
        crate::leanh::lean_inc(v_stx_798_);
        v___f_805_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__4 as *mut core::ffi::c_void, 8, 7);
        crate::leanh::lean_closure_set(v___f_805_, 0, v_toApplicative_801_);
        crate::leanh::lean_closure_set(v___f_805_, 1, v_stx_798_);
        crate::leanh::lean_closure_set(v___f_805_, 2, v_inst_796_);
        crate::leanh::lean_closure_set(v___f_805_, 3, v_f_797_);
        crate::leanh::lean_closure_set(v___f_805_, 4, v_toBind_802_);
        crate::leanh::lean_closure_set(v___f_805_, 5, v___f_804_);
        crate::leanh::lean_closure_set(v___f_805_, 6, v___f_803_);
        v___x_806_ = crate::leanh::lean_apply_2(v_f_797_, v_stx_798_, v_b_799_);
        v___x_807_ = crate::leanh::lean_apply_4(
            v_toBind_802_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_806_,
            v___f_805_,
        );
        return v___x_807_;
    } else {
        let mut v_toApplicative_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_798_);
        crate::leanh::lean_dec(v_f_797_);
        v_toApplicative_808_ = crate::leanh::lean_ctor_get(v_inst_796_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_808_);
        crate::leanh::lean_dec_ref(v_inst_796_);
        v_toPure_809_ = crate::leanh::lean_ctor_get(v_toApplicative_808_, 1);
        crate::leanh::lean_inc(v_toPure_809_);
        crate::leanh::lean_dec_ref(v_toApplicative_808_);
        v___x_810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_810_, 0, v_b_799_);
        v___x_811_ =
            crate::leanh::lean_apply_2(v_toPure_809_, crate::leanh::lean_box(0), v___x_810_);
        return v___x_811_;
    }
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__3(
    mut v_toApplicative_812_: *mut crate::leanh::LeanObject,
    mut v___x_813_: *mut crate::leanh::LeanObject,
    mut v_inst_814_: *mut crate::leanh::LeanObject,
    mut v_f_815_: *mut crate::leanh::LeanObject,
    mut v_toBind_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
    mut v___y_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_820_ = crate::leanh::lean_ctor_get(v___y_819_, 1);
    crate::leanh::lean_inc_n(v_snd_820_, 2);
    crate::leanh::lean_dec_ref(v___y_819_);
    v___f_821_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__2 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_821_, 0, v_toApplicative_812_);
    crate::leanh::lean_closure_set(v___f_821_, 1, v_snd_820_);
    crate::leanh::lean_closure_set(v___f_821_, 2, v___x_813_);
    v___x_822_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_814_, v_f_815_, v_a_817_, v_snd_820_);
    v___x_823_ = crate::leanh::lean_apply_4(
        v_toBind_816_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_822_,
        v___f_821_,
    );
    return v___x_823_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop(
    mut v_m_824_: *mut crate::leanh::LeanObject,
    mut v_inst_825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_826_: *mut crate::leanh::LeanObject,
    mut v_f_827_: *mut crate::leanh::LeanObject,
    mut v_stx_828_: *mut crate::leanh::LeanObject,
    mut v_b_829_: *mut crate::leanh::LeanObject,
    mut v_inst_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_825_, v_f_827_, v_stx_828_, v_b_829_);
    return v___x_831_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___boxed(
    mut v_m_832_: *mut crate::leanh::LeanObject,
    mut v_inst_833_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_834_: *mut crate::leanh::LeanObject,
    mut v_f_835_: *mut crate::leanh::LeanObject,
    mut v_stx_836_: *mut crate::leanh::LeanObject,
    mut v_b_837_: *mut crate::leanh::LeanObject,
    mut v_inst_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_839_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop(v_m_832_, v_inst_833_, v_00_u03b2_834_, v_f_835_, v_stx_836_, v_b_837_, v_inst_838_);
    crate::leanh::lean_dec(v_inst_838_);
    return v_res_839_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__0(
    mut v_toPure_840_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_842_ = crate::leanh::lean_ctor_get(v_____do__lift_841_, 0);
    crate::leanh::lean_inc(v_a_842_);
    crate::leanh::lean_dec_ref(v_____do__lift_841_);
    v___x_843_ = crate::leanh::lean_apply_2(v_toPure_840_, crate::leanh::lean_box(0), v_a_842_);
    return v___x_843_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__1(
    mut v_inst_844_: *mut crate::leanh::LeanObject,
    mut v_toBind_845_: *mut crate::leanh::LeanObject,
    mut v___f_846_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_847_: *mut crate::leanh::LeanObject,
    mut v_x_848_: *mut crate::leanh::LeanObject,
    mut v_init_849_: *mut crate::leanh::LeanObject,
    mut v_f_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_844_, v_f_850_, v_x_848_, v_init_849_);
    v___x_852_ = crate::leanh::lean_apply_4(
        v_toBind_845_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_851_,
        v___f_846_,
    );
    return v___x_852_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg(
    mut v_inst_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_854_ = crate::leanh::lean_ctor_get(v_inst_853_, 0);
    v_toBind_855_ = crate::leanh::lean_ctor_get(v_inst_853_, 1);
    crate::leanh::lean_inc(v_toBind_855_);
    v_toPure_856_ = crate::leanh::lean_ctor_get(v_toApplicative_854_, 1);
    crate::leanh::lean_inc(v_toPure_856_);
    v___f_857_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_857_, 0, v_toPure_856_);
    v___f_858_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__1 as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___f_858_, 0, v_inst_853_);
    crate::leanh::lean_closure_set(v___f_858_, 1, v_toBind_855_);
    crate::leanh::lean_closure_set(v___f_858_, 2, v___f_857_);
    return v___f_858_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad(
    mut v_m_859_: *mut crate::leanh::LeanObject,
    mut v_inst_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg(v_inst_860_);
    return v___x_861_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(
    mut v_as_896_: *mut crate::leanh::LeanObject,
    mut v_i_897_: usize,
    mut v_stop_898_: usize,
    mut v_b_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: usize = 0;
    let mut v___x_903_: usize = 0;
    let mut v___x_905_: u8 = 0;
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: u8 = 0;
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_905_ = lean_usize_dec_eq(v_i_897_, v_stop_898_);
                if v___x_905_ == 0 {
                    v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4;
                    v_a_907_ = lean_array_uget_borrowed(v_as_896_, v_i_897_);
                    crate::leanh::lean_inc(v_a_907_);
                    v___x_908_ = l_Lean_Syntax_isOfKind(v_a_907_, v___x_906_);
                    if v___x_908_ == 0 {
                        v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7;
                        crate::leanh::lean_inc(v_a_907_);
                        v___x_910_ = l_Lean_Syntax_isOfKind(v_a_907_, v___x_909_);
                        if v___x_910_ == 0 {
                            crate::leanh::lean_inc(v_a_907_);
                            v___x_911_ = lean_array_push(v_b_899_, v_a_907_);
                            v___y_901_ = v___x_911_;
                            state = 1;
                            continue;
                        } else {
                            v___x_912_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_913_ = l_Lean_Syntax_getArg(v_a_907_, v___x_912_);
                            v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9;
                            crate::leanh::lean_inc(v___x_913_);
                            v___x_915_ = l_Lean_Syntax_isOfKind(v___x_913_, v___x_914_);
                            if v___x_915_ == 0 {
                                crate::leanh::lean_dec(v___x_913_);
                                crate::leanh::lean_inc(v_a_907_);
                                v___x_916_ = lean_array_push(v_b_899_, v_a_907_);
                                v___y_901_ = v___x_916_;
                                state = 1;
                                continue;
                            } else {
                                v___x_917_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_918_ = l_Lean_Syntax_getArg(v___x_913_, v___x_912_);
                                crate::leanh::lean_dec(v___x_913_);
                                crate::leanh::lean_inc(v___x_918_);
                                v___x_919_ = l_Lean_Syntax_matchesNull(v___x_918_, v___x_917_);
                                if v___x_919_ == 0 {
                                    crate::leanh::lean_dec(v___x_918_);
                                    crate::leanh::lean_inc(v_a_907_);
                                    v___x_920_ = lean_array_push(v_b_899_, v_a_907_);
                                    v___y_901_ = v___x_920_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_921_ = l_Lean_Syntax_getArg(v___x_918_, v___x_912_);
                                    crate::leanh::lean_dec(v___x_918_);
                                    v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11;
                                    crate::leanh::lean_inc(v___x_921_);
                                    v___x_923_ = l_Lean_Syntax_isOfKind(v___x_921_, v___x_922_);
                                    if v___x_923_ == 0 {
                                        v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13;
                                        v___x_925_ = l_Lean_Syntax_isOfKind(v___x_921_, v___x_924_);
                                        if v___x_925_ == 0 {
                                            crate::leanh::lean_inc(v_a_907_);
                                            v___x_926_ = lean_array_push(v_b_899_, v_a_907_);
                                            v___y_901_ = v___x_926_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___y_901_ = v_b_899_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_921_);
                                        v___y_901_ = v_b_899_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___y_901_ = v_b_899_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_899_;
                }
            }
            1 => {
                v___x_902_ = 1usize;
                v___x_903_ = lean_usize_add(v_i_897_, v___x_902_);
                v_i_897_ = v___x_903_;
                v_b_899_ = v___y_901_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___boxed(
    mut v_as_927_: *mut crate::leanh::LeanObject,
    mut v_i_928_: *mut crate::leanh::LeanObject,
    mut v_stop_929_: *mut crate::leanh::LeanObject,
    mut v_b_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_931_: usize = 0;
    let mut v_stop_boxed_932_: usize = 0;
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_931_ = crate::leanh::lean_unbox_usize(v_i_928_);
    crate::leanh::lean_dec(v_i_928_);
    v_stop_boxed_932_ = crate::leanh::lean_unbox_usize(v_stop_929_);
    crate::leanh::lean_dec(v_stop_929_);
    v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_927_, v_i_boxed_931_, v_stop_boxed_932_, v_b_930_);
    crate::leanh::lean_dec_ref(v_as_927_);
    return v_res_933_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(
    mut v_as_936_: *mut crate::leanh::LeanObject,
    mut v_start_937_: *mut crate::leanh::LeanObject,
    mut v_stop_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    v___x_939_ = l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0;
    v___x_940_ = lean_nat_dec_lt(v_start_937_, v_stop_938_);
    if v___x_940_ == 0 {
        return v___x_939_;
    } else {
        let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_942_: u8 = 0;
        v___x_941_ = lean_array_get_size(v_as_936_);
        v___x_942_ = lean_nat_dec_le(v_stop_938_, v___x_941_);
        if v___x_942_ == 0 {
            let mut v___x_943_: u8 = 0;
            v___x_943_ = lean_nat_dec_lt(v_start_937_, v___x_941_);
            if v___x_943_ == 0 {
                return v___x_939_;
            } else {
                let mut v___x_944_: usize = 0;
                let mut v___x_945_: usize = 0;
                let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_944_ = lean_usize_of_nat(v_start_937_);
                v___x_945_ = lean_usize_of_nat(v___x_941_);
                v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_936_, v___x_944_, v___x_945_, v___x_939_);
                return v___x_946_;
            }
        } else {
            let mut v___x_947_: usize = 0;
            let mut v___x_948_: usize = 0;
            let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_947_ = lean_usize_of_nat(v_start_937_);
            v___x_948_ = lean_usize_of_nat(v_stop_938_);
            v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_936_, v___x_947_, v___x_948_, v___x_939_);
            return v___x_949_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___boxed(
    mut v_as_950_: *mut crate::leanh::LeanObject,
    mut v_start_951_: *mut crate::leanh::LeanObject,
    mut v_stop_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(v_as_950_, v_start_951_, v_stop_952_);
    crate::leanh::lean_dec(v_stop_952_);
    crate::leanh::lean_dec(v_start_951_);
    crate::leanh::lean_dec_ref(v_as_950_);
    return v_res_953_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(
    mut v_x_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    v___x_967_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1;
    crate::leanh::lean_inc(v_x_966_);
    v___x_968_ = l_Lean_Syntax_isOfKind(v_x_966_, v___x_967_);
    if v___x_968_ == 0 {
        let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_966_);
        v___x_969_ = crate::leanh::lean_box(0);
        return v___x_969_;
    } else {
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: u8 = 0;
        v___x_970_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_971_ = l_Lean_Syntax_getArg(v_x_966_, v___x_970_);
        crate::leanh::lean_dec(v_x_966_);
        v___x_972_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3;
        crate::leanh::lean_inc(v___x_971_);
        v___x_973_ = l_Lean_Syntax_isOfKind(v___x_971_, v___x_972_);
        if v___x_973_ == 0 {
            let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_971_);
            v___x_974_ = crate::leanh::lean_box(0);
            return v___x_974_;
        } else {
            let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_978_: u8 = 0;
            v___x_975_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_976_ = crate::leanh::lean_unsigned_to_nat(4);
            v___x_977_ = l_Lean_Syntax_getArg(v___x_971_, v___x_976_);
            crate::leanh::lean_inc(v___x_977_);
            v___x_978_ = l_Lean_Syntax_matchesNull(v___x_977_, v___x_975_);
            if v___x_978_ == 0 {
                let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_977_);
                crate::leanh::lean_dec(v___x_971_);
                v___x_979_ = crate::leanh::lean_box(0);
                return v___x_979_;
            } else {
                let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_xs_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_980_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_981_ = l_Lean_Syntax_getArg(v___x_971_, v___x_980_);
                crate::leanh::lean_dec(v___x_971_);
                v_id_982_ = l_Lean_Syntax_getArg(v___x_977_, v___x_970_);
                crate::leanh::lean_dec(v___x_977_);
                v_x_983_ = l_Lean_Syntax_getArgs(v___x_981_);
                crate::leanh::lean_dec(v___x_981_);
                v___x_984_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_x_983_);
                crate::leanh::lean_dec_ref(v_x_983_);
                v___x_985_ = lean_array_get_size(v___x_984_);
                v_xs_986_ = l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(v___x_984_, v___x_970_, v___x_985_);
                crate::leanh::lean_dec_ref(v___x_984_);
                v___x_987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_987_, 0, v_id_982_);
                crate::leanh::lean_ctor_set(v___x_987_, 1, v_xs_986_);
                v___x_988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_988_, 0, v___x_987_);
                return v___x_988_;
            }
        }
    }
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_989_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_993_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_994_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_994_, 0, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_994_, 2, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_994_, 3, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_994_, 4, v___x_992_);
    crate::leanh::lean_ctor_set(v___x_994_, 5, v___x_992_);
    crate::leanh::lean_ctor_set(v___x_994_, 6, v___x_992_);
    crate::leanh::lean_ctor_set(v___x_994_, 7, v___x_992_);
    crate::leanh::lean_ctor_set(v___x_994_, 8, v___x_992_);
    crate::leanh::lean_ctor_set(v___x_994_, 9, v___x_992_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_996_ = lean_mk_empty_array_with_capacity(v___x_995_);
    v___x_997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_997_, 0, v___x_996_);
    return v___x_997_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_998_: usize = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = 5usize;
    v___x_999_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1000_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
    v___x_1002_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1003_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    crate::leanh::lean_ctor_set(v___x_1003_, 1, v___x_1001_);
    crate::leanh::lean_ctor_set(v___x_1003_, 2, v___x_999_);
    crate::leanh::lean_ctor_set(v___x_1003_, 3, v___x_999_);
    crate::leanh::lean_ctor_set_usize(v___x_1003_, 4, v___x_998_);
    return v___x_1003_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = crate::leanh::lean_box(1);
    v___x_1005_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4);
    v___x_1006_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1007_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1007_, 0, v___x_1006_);
    crate::leanh::lean_ctor_set(v___x_1007_, 1, v___x_1005_);
    crate::leanh::lean_ctor_set(v___x_1007_, 2, v___x_1004_);
    return v___x_1007_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(
    mut v_msgData_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = lean_st_ref_get(v___y_1009_);
    v_env_1012_ = crate::leanh::lean_ctor_get(v___x_1011_, 0);
    crate::leanh::lean_inc_ref(v_env_1012_);
    crate::leanh::lean_dec(v___x_1011_);
    v___x_1013_ = lean_st_ref_get(v___y_1009_);
    v_scopes_1014_ = crate::leanh::lean_ctor_get(v___x_1013_, 2);
    crate::leanh::lean_inc(v_scopes_1014_);
    crate::leanh::lean_dec(v___x_1013_);
    v___x_1015_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1016_ = l_List_head_x21___redArg(v___x_1015_, v_scopes_1014_);
    crate::leanh::lean_dec(v_scopes_1014_);
    v_opts_1017_ = crate::leanh::lean_ctor_get(v___x_1016_, 1);
    crate::leanh::lean_inc_ref(v_opts_1017_);
    crate::leanh::lean_dec(v___x_1016_);
    v___x_1018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2);
    v___x_1019_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5);
    v___x_1020_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1020_, 0, v_env_1012_);
    crate::leanh::lean_ctor_set(v___x_1020_, 1, v___x_1018_);
    crate::leanh::lean_ctor_set(v___x_1020_, 2, v___x_1019_);
    crate::leanh::lean_ctor_set(v___x_1020_, 3, v_opts_1017_);
    v___x_1021_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1020_);
    crate::leanh::lean_ctor_set(v___x_1021_, 1, v_msgData_1008_);
    v___x_1022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1022_, 0, v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msgData_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_1023_, v___y_1024_);
    crate::leanh::lean_dec(v___y_1024_);
    return v_res_1026_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(
    mut v_opts_1027_: *mut crate::leanh::LeanObject,
    mut v_opt_1028_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1029_ = crate::leanh::lean_ctor_get(v_opt_1028_, 0);
    v_defValue_1030_ = crate::leanh::lean_ctor_get(v_opt_1028_, 1);
    v_map_1031_ = crate::leanh::lean_ctor_get(v_opts_1027_, 0);
    v___x_1032_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1031_,
            v_name_1029_,
        );
    if crate::leanh::lean_obj_tag(v___x_1032_) == 0 {
        let mut v___x_1033_: u8 = 0;
        v___x_1033_ = (crate::leanh::lean_unbox(v_defValue_1030_) as u8);
        return v___x_1033_;
    } else {
        let mut v_val_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1034_ = crate::leanh::lean_ctor_get(v___x_1032_, 0);
        crate::leanh::lean_inc(v_val_1034_);
        crate::leanh::lean_dec_ref_known(v___x_1032_, 1);
        if crate::leanh::lean_obj_tag(v_val_1034_) == 1 {
            let mut v_v_1035_: u8 = 0;
            v_v_1035_ = crate::leanh::lean_ctor_get_uint8(v_val_1034_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1034_, 0);
            return v_v_1035_;
        } else {
            let mut v___x_1036_: u8 = 0;
            crate::leanh::lean_dec(v_val_1034_);
            v___x_1036_ = (crate::leanh::lean_unbox(v_defValue_1030_) as u8);
            return v___x_1036_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2___boxed(
    mut v_opts_1037_: *mut crate::leanh::LeanObject,
    mut v_opt_1038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1039_: u8 = 0;
    let mut v_r_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_1037_, v_opt_1038_);
    crate::leanh::lean_dec_ref(v_opt_1038_);
    crate::leanh::lean_dec_ref(v_opts_1037_);
    v_r_1040_ = crate::leanh::lean_box((v_res_1039_) as usize);
    return v_r_1040_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(
    mut v___y_1042_: u8,
    mut v_suppressElabErrors_1043_: u8,
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1044_) == 1 {
        let mut v_pre_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1045_ = crate::leanh::lean_ctor_get(v_x_1044_, 0);
        if crate::leanh::lean_obj_tag(v_pre_1045_) == 0 {
            let mut v_str_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1048_: u8 = 0;
            v_str_1046_ = crate::leanh::lean_ctor_get(v_x_1044_, 1);
            v___x_1047_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0;
            v___x_1048_ = lean_string_dec_eq(v_str_1046_, v___x_1047_);
            if v___x_1048_ == 0 {
                return v___y_1042_;
            } else {
                return v_suppressElabErrors_1043_;
            }
        } else {
            return v___y_1042_;
        }
    } else {
        return v___y_1042_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed(
    mut v___y_1049_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1050_: *mut crate::leanh::LeanObject,
    mut v_x_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4509__boxed_1052_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1053_: u8 = 0;
    let mut v_res_1054_: u8 = 0;
    let mut v_r_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4509__boxed_1052_ = (crate::leanh::lean_unbox(v___y_1049_) as u8);
    v_suppressElabErrors_boxed_1053_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1050_) as u8);
    v_res_1054_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(v___y_4509__boxed_1052_, v_suppressElabErrors_boxed_1053_, v_x_1051_);
    crate::leanh::lean_dec(v_x_1051_);
    v_r_1055_ = crate::leanh::lean_box((v_res_1054_) as usize);
    return v_r_1055_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(
    mut v_ref_1057_: *mut crate::leanh::LeanObject,
    mut v_msgData_1058_: *mut crate::leanh::LeanObject,
    mut v_severity_1059_: u8,
    mut v_isSilent_1060_: u8,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1068_: u8 = 0;
    let mut v___y_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1071_: u8 = 0;
    let mut v___y_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1096_: u8 = 0;
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_a_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1122_: u8 = 0;
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1126_: u8 = 0;
    let mut v___y_1128_: u8 = 0;
    let mut v___y_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1130_: u8 = 0;
    let mut v___y_1131_: u8 = 0;
    let mut v___y_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1135_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1141_: u8 = 0;
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v___y_1156_: u8 = 0;
    let mut v___y_1157_: u8 = 0;
    let mut v___y_1158_: u8 = 0;
    let mut v___y_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1164_: u8 = 0;
    let mut v___y_1165_: u8 = 0;
    let mut v___y_1166_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___y_1183_: u8 = 0;
    let mut v___y_1184_: u8 = 0;
    let mut v___y_1185_: u8 = 0;
    let mut v___y_1187_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1181_ = 2;
                v___x_1199_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1059_, v___x_1181_);
                if v___x_1199_ == 0 {
                    v___y_1187_ = v___x_1199_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1058_);
                    v___x_1200_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1058_);
                    v___y_1187_ = v___x_1200_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1073_ = l_Lean_Elab_Command_getScope___redArg(v___y_1072_);
                if crate::leanh::lean_obj_tag(v___x_1073_) == 0 {
                    v_a_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    crate::leanh::lean_inc(v_a_1074_);
                    crate::leanh::lean_dec_ref_known(v___x_1073_, 1);
                    v___x_1075_ = l_Lean_Elab_Command_getScope___redArg(v___y_1072_);
                    if crate::leanh::lean_obj_tag(v___x_1075_) == 0 {
                        v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                        v_isSharedCheck_1110_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                        if v_isSharedCheck_1110_ == 0 {
                            v___x_1078_ = v___x_1075_;
                            v_isShared_1079_ = v_isSharedCheck_1110_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1076_);
                            crate::leanh::lean_dec(v___x_1075_);
                            v___x_1078_ = crate::leanh::lean_box(0);
                            v_isShared_1079_ = v_isSharedCheck_1110_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1074_);
                        crate::leanh::lean_dec_ref(v___y_1070_);
                        crate::leanh::lean_dec_ref(v___y_1069_);
                        crate::leanh::lean_dec(v___y_1067_);
                        v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                        v_isSharedCheck_1118_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                        if v_isSharedCheck_1118_ == 0 {
                            v___x_1113_ = v___x_1075_;
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1111_);
                            crate::leanh::lean_dec(v___x_1075_);
                            v___x_1113_ = crate::leanh::lean_box(0);
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1070_);
                    crate::leanh::lean_dec_ref(v___y_1069_);
                    crate::leanh::lean_dec(v___y_1067_);
                    v_a_1119_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    v_isSharedCheck_1126_ = (!crate::leanh::lean_is_exclusive(v___x_1073_)) as u8;
                    if v_isSharedCheck_1126_ == 0 {
                        v___x_1121_ = v___x_1073_;
                        v_isShared_1122_ = v_isSharedCheck_1126_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1119_);
                        crate::leanh::lean_dec(v___x_1073_);
                        v___x_1121_ = crate::leanh::lean_box(0);
                        v_isShared_1122_ = v_isSharedCheck_1126_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1080_ = lean_st_ref_take(v___y_1072_);
                v_currNamespace_1081_ = crate::leanh::lean_ctor_get(v_a_1074_, 2);
                crate::leanh::lean_inc(v_currNamespace_1081_);
                crate::leanh::lean_dec(v_a_1074_);
                v_openDecls_1082_ = crate::leanh::lean_ctor_get(v_a_1076_, 3);
                crate::leanh::lean_inc(v_openDecls_1082_);
                crate::leanh::lean_dec(v_a_1076_);
                v_env_1083_ = crate::leanh::lean_ctor_get(v___x_1080_, 0);
                v_messages_1084_ = crate::leanh::lean_ctor_get(v___x_1080_, 1);
                v_scopes_1085_ = crate::leanh::lean_ctor_get(v___x_1080_, 2);
                v_usedQuotCtxts_1086_ = crate::leanh::lean_ctor_get(v___x_1080_, 3);
                v_nextMacroScope_1087_ = crate::leanh::lean_ctor_get(v___x_1080_, 4);
                v_maxRecDepth_1088_ = crate::leanh::lean_ctor_get(v___x_1080_, 5);
                v_ngen_1089_ = crate::leanh::lean_ctor_get(v___x_1080_, 6);
                v_auxDeclNGen_1090_ = crate::leanh::lean_ctor_get(v___x_1080_, 7);
                v_infoState_1091_ = crate::leanh::lean_ctor_get(v___x_1080_, 8);
                v_traceState_1092_ = crate::leanh::lean_ctor_get(v___x_1080_, 9);
                v_snapshotTasks_1093_ = crate::leanh::lean_ctor_get(v___x_1080_, 10);
                v_isSharedCheck_1109_ = (!crate::leanh::lean_is_exclusive(v___x_1080_)) as u8;
                if v_isSharedCheck_1109_ == 0 {
                    v___x_1095_ = v___x_1080_;
                    v_isShared_1096_ = v_isSharedCheck_1109_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1093_);
                    crate::leanh::lean_inc(v_traceState_1092_);
                    crate::leanh::lean_inc(v_infoState_1091_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1090_);
                    crate::leanh::lean_inc(v_ngen_1089_);
                    crate::leanh::lean_inc(v_maxRecDepth_1088_);
                    crate::leanh::lean_inc(v_nextMacroScope_1087_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1086_);
                    crate::leanh::lean_inc(v_scopes_1085_);
                    crate::leanh::lean_inc(v_messages_1084_);
                    crate::leanh::lean_inc(v_env_1083_);
                    crate::leanh::lean_dec(v___x_1080_);
                    v___x_1095_ = crate::leanh::lean_box(0);
                    v_isShared_1096_ = v_isSharedCheck_1109_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1097_, 0, v_currNamespace_1081_);
                crate::leanh::lean_ctor_set(v___x_1097_, 1, v_openDecls_1082_);
                v___x_1098_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1098_, 0, v___x_1097_);
                crate::leanh::lean_ctor_set(v___x_1098_, 1, v___y_1069_);
                crate::leanh::lean_inc_ref(v___y_1066_);
                crate::leanh::lean_inc_ref(v___y_1065_);
                v___x_1099_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1099_, 0, v___y_1065_);
                crate::leanh::lean_ctor_set(v___x_1099_, 1, v___y_1070_);
                crate::leanh::lean_ctor_set(v___x_1099_, 2, v___y_1067_);
                crate::leanh::lean_ctor_set(v___x_1099_, 3, v___y_1066_);
                crate::leanh::lean_ctor_set(v___x_1099_, 4, v___x_1098_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1099_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1071_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1099_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1068_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1099_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1060_,
                );
                v___x_1100_ = l_Lean_MessageLog_add(v___x_1099_, v_messages_1084_);
                if v_isShared_1096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1095_, 1, v___x_1100_);
                    v___x_1102_ = v___x_1095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_env_1083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_scopes_1085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_usedQuotCtxts_1086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_nextMacroScope_1087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_maxRecDepth_1088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 6, v_ngen_1089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 7, v_auxDeclNGen_1090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 8, v_infoState_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 9, v_traceState_1092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 10, v_snapshotTasks_1093_);
                    v___x_1102_ = v_reuseFailAlloc_1108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1103_ = lean_st_ref_set(v___y_1072_, v___x_1102_);
                v___x_1104_ = crate::leanh::lean_box(0);
                if v_isShared_1079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1104_);
                    v___x_1106_ = v___x_1078_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
                    v___x_1106_ = v_reuseFailAlloc_1107_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1106_;
            }
            6 => {
                if v_isShared_1114_ == 0 {
                    v___x_1116_ = v___x_1113_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1116_;
            }
            8 => {
                if v_isShared_1122_ == 0 {
                    v___x_1124_ = v___x_1121_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
                    v___x_1124_ = v_reuseFailAlloc_1125_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1124_;
            }
            10 => {
                v_fileName_1133_ = crate::leanh::lean_ctor_get(v___y_1061_, 0);
                v_fileMap_1134_ = crate::leanh::lean_ctor_get(v___y_1061_, 1);
                v_suppressElabErrors_1135_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1061_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_1136_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1058_,
                    );
                v___x_1137_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v___x_1136_, v___y_1062_);
                v_a_1138_ = crate::leanh::lean_ctor_get(v___x_1137_, 0);
                v_isSharedCheck_1154_ = (!crate::leanh::lean_is_exclusive(v___x_1137_)) as u8;
                if v_isSharedCheck_1154_ == 0 {
                    v___x_1140_ = v___x_1137_;
                    v_isShared_1141_ = v_isSharedCheck_1154_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1138_);
                    crate::leanh::lean_dec(v___x_1137_);
                    v___x_1140_ = crate::leanh::lean_box(0);
                    v_isShared_1141_ = v_isSharedCheck_1154_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1134_, 2);
                v___x_1142_ = l_Lean_FileMap_toPosition(v_fileMap_1134_, v___y_1129_);
                crate::leanh::lean_dec(v___y_1129_);
                v___x_1143_ = l_Lean_FileMap_toPosition(v_fileMap_1134_, v___y_1132_);
                crate::leanh::lean_dec(v___y_1132_);
                v___x_1144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1143_);
                v___x_1145_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0;
                if v_suppressElabErrors_1135_ == 0 {
                    crate::leanh::lean_del_object(v___x_1140_);
                    v___y_1065_ = v_fileName_1133_;
                    v___y_1066_ = v___x_1145_;
                    v___y_1067_ = v___x_1144_;
                    v___y_1068_ = v___y_1130_;
                    v___y_1069_ = v_a_1138_;
                    v___y_1070_ = v___x_1142_;
                    v___y_1071_ = v___y_1131_;
                    v___y_1072_ = v___y_1062_;
                    state = 1;
                    continue;
                } else {
                    v___x_1146_ = crate::leanh::lean_box((v___y_1128_) as usize);
                    v___x_1147_ = crate::leanh::lean_box((v_suppressElabErrors_1135_) as usize);
                    v___f_1148_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1148_, 0, v___x_1146_);
                    crate::leanh::lean_closure_set(v___f_1148_, 1, v___x_1147_);
                    crate::leanh::lean_inc(v_a_1138_);
                    v___x_1149_ = l_Lean_MessageData_hasTag(v___f_1148_, v_a_1138_);
                    if v___x_1149_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1144_, 1);
                        crate::leanh::lean_dec_ref(v___x_1142_);
                        crate::leanh::lean_dec(v_a_1138_);
                        v___x_1150_ = crate::leanh::lean_box(0);
                        if v_isShared_1141_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1150_);
                            v___x_1152_ = v___x_1140_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1153_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
                            v___x_1152_ = v_reuseFailAlloc_1153_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1140_);
                        v___y_1065_ = v_fileName_1133_;
                        v___y_1066_ = v___x_1145_;
                        v___y_1067_ = v___x_1144_;
                        v___y_1068_ = v___y_1130_;
                        v___y_1069_ = v_a_1138_;
                        v___y_1070_ = v___x_1142_;
                        v___y_1071_ = v___y_1131_;
                        v___y_1072_ = v___y_1062_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1152_;
            }
            13 => {
                v___x_1161_ = l_Lean_Syntax_getTailPos_x3f(v___y_1159_, v___y_1158_);
                crate::leanh::lean_dec(v___y_1159_);
                if crate::leanh::lean_obj_tag(v___x_1161_) == 0 {
                    crate::leanh::lean_inc(v___y_1160_);
                    v___y_1128_ = v___y_1156_;
                    v___y_1129_ = v___y_1160_;
                    v___y_1130_ = v___y_1157_;
                    v___y_1131_ = v___y_1158_;
                    v___y_1132_ = v___y_1160_;
                    state = 10;
                    continue;
                } else {
                    v_val_1162_ = crate::leanh::lean_ctor_get(v___x_1161_, 0);
                    crate::leanh::lean_inc(v_val_1162_);
                    crate::leanh::lean_dec_ref_known(v___x_1161_, 1);
                    v___y_1128_ = v___y_1156_;
                    v___y_1129_ = v___y_1160_;
                    v___y_1130_ = v___y_1157_;
                    v___y_1131_ = v___y_1158_;
                    v___y_1132_ = v_val_1162_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1167_ = l_Lean_Elab_Command_getRef___redArg(v___y_1061_);
                if crate::leanh::lean_obj_tag(v___x_1167_) == 0 {
                    v_a_1168_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    crate::leanh::lean_inc(v_a_1168_);
                    crate::leanh::lean_dec_ref_known(v___x_1167_, 1);
                    v_ref_1169_ = l_Lean_replaceRef(v_ref_1057_, v_a_1168_);
                    crate::leanh::lean_dec(v_a_1168_);
                    v___x_1170_ = l_Lean_Syntax_getPos_x3f(v_ref_1169_, v___y_1165_);
                    if crate::leanh::lean_obj_tag(v___x_1170_) == 0 {
                        v___x_1171_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_1156_ = v___y_1164_;
                        v___y_1157_ = v___y_1166_;
                        v___y_1158_ = v___y_1165_;
                        v___y_1159_ = v_ref_1169_;
                        v___y_1160_ = v___x_1171_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1172_ = crate::leanh::lean_ctor_get(v___x_1170_, 0);
                        crate::leanh::lean_inc(v_val_1172_);
                        crate::leanh::lean_dec_ref_known(v___x_1170_, 1);
                        v___y_1156_ = v___y_1164_;
                        v___y_1157_ = v___y_1166_;
                        v___y_1158_ = v___y_1165_;
                        v___y_1159_ = v_ref_1169_;
                        v___y_1160_ = v_val_1172_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1058_);
                    v_a_1173_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    v_isSharedCheck_1180_ = (!crate::leanh::lean_is_exclusive(v___x_1167_)) as u8;
                    if v_isSharedCheck_1180_ == 0 {
                        v___x_1175_ = v___x_1167_;
                        v_isShared_1176_ = v_isSharedCheck_1180_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1173_);
                        crate::leanh::lean_dec(v___x_1167_);
                        v___x_1175_ = crate::leanh::lean_box(0);
                        v_isShared_1176_ = v_isSharedCheck_1180_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1176_ == 0 {
                    v___x_1178_ = v___x_1175_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1178_;
            }
            17 => {
                if v___y_1185_ == 0 {
                    v___y_1164_ = v___y_1183_;
                    v___y_1165_ = v___y_1184_;
                    v___y_1166_ = v_severity_1059_;
                    state = 14;
                    continue;
                } else {
                    v___y_1164_ = v___y_1183_;
                    v___y_1165_ = v___y_1184_;
                    v___y_1166_ = v___x_1181_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1187_ == 0 {
                    v___x_1188_ = lean_st_ref_get(v___y_1062_);
                    v_scopes_1189_ = crate::leanh::lean_ctor_get(v___x_1188_, 2);
                    crate::leanh::lean_inc(v_scopes_1189_);
                    crate::leanh::lean_dec(v___x_1188_);
                    v___x_1190_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1191_ = l_List_head_x21___redArg(v___x_1190_, v_scopes_1189_);
                    crate::leanh::lean_dec(v_scopes_1189_);
                    v_opts_1192_ = crate::leanh::lean_ctor_get(v___x_1191_, 1);
                    crate::leanh::lean_inc_ref(v_opts_1192_);
                    crate::leanh::lean_dec(v___x_1191_);
                    v___x_1193_ = 1;
                    v___x_1194_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1059_, v___x_1193_);
                    if v___x_1194_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_1192_);
                        v___y_1183_ = v___y_1187_;
                        v___y_1184_ = v___y_1187_;
                        v___y_1185_ = v___x_1194_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1195_ = l_Lean_warningAsError;
                        v___x_1196_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_1192_, v___x_1195_);
                        crate::leanh::lean_dec_ref(v_opts_1192_);
                        v___y_1183_ = v___y_1187_;
                        v___y_1184_ = v___y_1187_;
                        v___y_1185_ = v___x_1196_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1058_);
                    v___x_1197_ = crate::leanh::lean_box(0);
                    v___x_1198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
                    return v___x_1198_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___boxed(
    mut v_ref_1201_: *mut crate::leanh::LeanObject,
    mut v_msgData_1202_: *mut crate::leanh::LeanObject,
    mut v_severity_1203_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1208_: u8 = 0;
    let mut v_isSilent_boxed_1209_: u8 = 0;
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1208_ = (crate::leanh::lean_unbox(v_severity_1203_) as u8);
    v_isSilent_boxed_1209_ = (crate::leanh::lean_unbox(v_isSilent_1204_) as u8);
    v_res_1210_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_1201_, v_msgData_1202_, v_severity_boxed_1208_, v_isSilent_boxed_1209_, v___y_1205_, v___y_1206_);
    crate::leanh::lean_dec(v___y_1206_);
    crate::leanh::lean_dec_ref(v___y_1205_);
    crate::leanh::lean_dec(v_ref_1201_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(
    mut v_ref_1211_: *mut crate::leanh::LeanObject,
    mut v_msgData_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = 2;
    v___x_1217_ = 0;
    v___x_1218_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_1211_, v_msgData_1212_, v___x_1216_, v___x_1217_, v___y_1213_, v___y_1214_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0___boxed(
    mut v_ref_1219_: *mut crate::leanh::LeanObject,
    mut v_msgData_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_ref_1219_, v_msgData_1220_, v___y_1221_, v___y_1222_);
    crate::leanh::lean_dec(v___y_1222_);
    crate::leanh::lean_dec_ref(v___y_1221_);
    crate::leanh::lean_dec(v_ref_1219_);
    return v_res_1224_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0;
    v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2;
    v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
    return v___x_1230_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4;
    v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
    return v___x_1233_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6;
    v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
    return v___x_1236_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(
    mut v_fst_1237_: *mut crate::leanh::LeanObject,
    mut v_as_1238_: *mut crate::leanh::LeanObject,
    mut v_sz_1239_: usize,
    mut v_i_1240_: usize,
    mut v_b_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: usize = 0;
    let mut v___x_1263_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1245_ = lean_usize_dec_lt(v_i_1240_, v_sz_1239_);
                if v___x_1245_ == 0 {
                    crate::leanh::lean_dec(v_fst_1237_);
                    v___x_1246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1246_, 0, v_b_1241_);
                    return v___x_1246_;
                } else {
                    v_a_1247_ = lean_array_uget_borrowed(v_as_1238_, v_i_1240_);
                    v___x_1248_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1);
                    crate::leanh::lean_inc(v_a_1247_);
                    v___x_1249_ = l_Lean_MessageData_ofSyntax(v_a_1247_);
                    crate::leanh::lean_inc_ref(v___x_1249_);
                    v___x_1250_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1248_);
                    crate::leanh::lean_ctor_set(v___x_1250_, 1, v___x_1249_);
                    v___x_1251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3);
                    v___x_1252_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1250_);
                    crate::leanh::lean_ctor_set(v___x_1252_, 1, v___x_1251_);
                    crate::leanh::lean_inc(v_fst_1237_);
                    v___x_1253_ = l_Lean_MessageData_ofSyntax(v_fst_1237_);
                    v___x_1254_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1254_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
                    v___x_1255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5);
                    v___x_1256_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1254_);
                    crate::leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
                    v___x_1257_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1257_, 0, v___x_1256_);
                    crate::leanh::lean_ctor_set(v___x_1257_, 1, v___x_1249_);
                    v___x_1258_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7);
                    v___x_1259_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1259_, 0, v___x_1257_);
                    crate::leanh::lean_ctor_set(v___x_1259_, 1, v___x_1258_);
                    v___x_1260_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_a_1247_, v___x_1259_, v___y_1242_, v___y_1243_);
                    if crate::leanh::lean_obj_tag(v___x_1260_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1260_, 1);
                        v___x_1261_ = crate::leanh::lean_box(0);
                        v___x_1262_ = 1usize;
                        v___x_1263_ = lean_usize_add(v_i_1240_, v___x_1262_);
                        v_i_1240_ = v___x_1263_;
                        v_b_1241_ = v___x_1261_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1237_);
                        return v___x_1260_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___boxed(
    mut v_fst_1265_: *mut crate::leanh::LeanObject,
    mut v_as_1266_: *mut crate::leanh::LeanObject,
    mut v_sz_1267_: *mut crate::leanh::LeanObject,
    mut v_i_1268_: *mut crate::leanh::LeanObject,
    mut v_b_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1273_: usize = 0;
    let mut v_i_boxed_1274_: usize = 0;
    let mut v_res_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1273_ = crate::leanh::lean_unbox_usize(v_sz_1267_);
    crate::leanh::lean_dec(v_sz_1267_);
    v_i_boxed_1274_ = crate::leanh::lean_unbox_usize(v_i_1268_);
    crate::leanh::lean_dec(v_i_1268_);
    v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_1265_, v_as_1266_, v_sz_boxed_1273_, v_i_boxed_1274_, v_b_1269_, v___y_1270_, v___y_1271_);
    crate::leanh::lean_dec(v___y_1271_);
    crate::leanh::lean_dec_ref(v___y_1270_);
    crate::leanh::lean_dec_ref(v_as_1266_);
    return v_res_1275_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(
    mut v_stx_1276_: *mut crate::leanh::LeanObject,
    mut v_b_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v_fst_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_a_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1318_: usize = 0;
    let mut v___x_1319_: usize = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = l_Lean_Syntax_isQuot(v_stx_1276_);
                if v___x_1312_ == 0 {
                    v___x_1313_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_stx_1276_);
                    v___x_1314_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(v_stx_1276_);
                    if crate::leanh::lean_obj_tag(v___x_1314_) == 1 {
                        v_val_1315_ = crate::leanh::lean_ctor_get(v___x_1314_, 0);
                        crate::leanh::lean_inc(v_val_1315_);
                        crate::leanh::lean_dec_ref_known(v___x_1314_, 1);
                        v_fst_1316_ = crate::leanh::lean_ctor_get(v_val_1315_, 0);
                        crate::leanh::lean_inc(v_fst_1316_);
                        v_snd_1317_ = crate::leanh::lean_ctor_get(v_val_1315_, 1);
                        crate::leanh::lean_inc(v_snd_1317_);
                        crate::leanh::lean_dec(v_val_1315_);
                        v_sz_1318_ = lean_array_size(v_snd_1317_);
                        v___x_1319_ = 0usize;
                        v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_1316_, v_snd_1317_, v_sz_1318_, v___x_1319_, v___x_1313_, v___y_1278_, v___y_1279_);
                        crate::leanh::lean_dec(v_snd_1317_);
                        if crate::leanh::lean_obj_tag(v___x_1320_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1320_, 1);
                            v_a_1286_ = v___x_1313_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_stx_1276_);
                            v_a_1321_ = crate::leanh::lean_ctor_get(v___x_1320_, 0);
                            v_isSharedCheck_1328_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1320_)) as u8;
                            if v_isSharedCheck_1328_ == 0 {
                                v___x_1323_ = v___x_1320_;
                                v_isShared_1324_ = v_isSharedCheck_1328_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1321_);
                                crate::leanh::lean_dec(v___x_1320_);
                                v___x_1323_ = crate::leanh::lean_box(0);
                                v_isShared_1324_ = v_isSharedCheck_1328_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1314_);
                        v_a_1286_ = v___x_1313_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_1276_);
                    v___x_1329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1329_, 0, v_b_1277_);
                    v___x_1330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1329_);
                    return v___x_1330_;
                }
            }
            1 => {
                v___x_1283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1283_, 0, v_b_1282_);
                v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
                return v___x_1284_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_stx_1276_) == 1 {
                    v_args_1287_ = crate::leanh::lean_ctor_get(v_stx_1276_, 2);
                    crate::leanh::lean_inc_ref(v_args_1287_);
                    crate::leanh::lean_dec_ref_known(v_stx_1276_, 3);
                    v___x_1288_ = crate::leanh::lean_box(0);
                    v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1288_);
                    crate::leanh::lean_ctor_set(v___x_1289_, 1, v_a_1286_);
                    v_sz_1290_ = lean_array_size(v_args_1287_);
                    v___x_1291_ = 0usize;
                    v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_args_1287_, v_sz_1290_, v___x_1291_, v___x_1289_, v___y_1278_, v___y_1279_);
                    crate::leanh::lean_dec_ref(v_args_1287_);
                    if crate::leanh::lean_obj_tag(v___x_1292_) == 0 {
                        v_a_1293_ = crate::leanh::lean_ctor_get(v___x_1292_, 0);
                        v_isSharedCheck_1303_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1292_)) as u8;
                        if v_isSharedCheck_1303_ == 0 {
                            v___x_1295_ = v___x_1292_;
                            v_isShared_1296_ = v_isSharedCheck_1303_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1293_);
                            crate::leanh::lean_dec(v___x_1292_);
                            v___x_1295_ = crate::leanh::lean_box(0);
                            v_isShared_1296_ = v_isSharedCheck_1303_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1304_ = crate::leanh::lean_ctor_get(v___x_1292_, 0);
                        v_isSharedCheck_1311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1292_)) as u8;
                        if v_isSharedCheck_1311_ == 0 {
                            v___x_1306_ = v___x_1292_;
                            v_isShared_1307_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1304_);
                            crate::leanh::lean_dec(v___x_1292_);
                            v___x_1306_ = crate::leanh::lean_box(0);
                            v_isShared_1307_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_1276_);
                    v_b_1282_ = v_a_1286_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_fst_1297_ = crate::leanh::lean_ctor_get(v_a_1293_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1297_) == 0 {
                    crate::leanh::lean_del_object(v___x_1295_);
                    v_snd_1298_ = crate::leanh::lean_ctor_get(v_a_1293_, 1);
                    crate::leanh::lean_inc(v_snd_1298_);
                    crate::leanh::lean_dec(v_a_1293_);
                    v_b_1282_ = v_snd_1298_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1297_);
                    crate::leanh::lean_dec(v_a_1293_);
                    v_val_1299_ = crate::leanh::lean_ctor_get(v_fst_1297_, 0);
                    crate::leanh::lean_inc(v_val_1299_);
                    crate::leanh::lean_dec_ref_known(v_fst_1297_, 1);
                    if v_isShared_1296_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1295_, 0, v_val_1299_);
                        v___x_1301_ = v___x_1295_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1299_);
                        v___x_1301_ = v_reuseFailAlloc_1302_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1301_;
            }
            5 => {
                if v_isShared_1307_ == 0 {
                    v___x_1309_ = v___x_1306_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1309_;
            }
            7 => {
                if v_isShared_1324_ == 0 {
                    v___x_1326_ = v___x_1323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(
    mut v_as_1331_: *mut crate::leanh::LeanObject,
    mut v_sz_1332_: usize,
    mut v_i_1333_: usize,
    mut v_b_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: usize = 0;
    let mut v___x_1362_: usize = 0;
    let mut v_reuseFailAlloc_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_unused_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1338_ = lean_usize_dec_lt(v_i_1333_, v_sz_1332_);
                if v___x_1338_ == 0 {
                    v___x_1339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1339_, 0, v_b_1334_);
                    return v___x_1339_;
                } else {
                    v_snd_1340_ = crate::leanh::lean_ctor_get(v_b_1334_, 1);
                    v_isSharedCheck_1374_ = (!crate::leanh::lean_is_exclusive(v_b_1334_)) as u8;
                    if v_isSharedCheck_1374_ == 0 {
                        v_unused_1375_ = crate::leanh::lean_ctor_get(v_b_1334_, 0);
                        crate::leanh::lean_dec(v_unused_1375_);
                        v___x_1342_ = v_b_1334_;
                        v_isShared_1343_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1340_);
                        crate::leanh::lean_dec(v_b_1334_);
                        v___x_1342_ = crate::leanh::lean_box(0);
                        v_isShared_1343_ = v_isSharedCheck_1374_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1344_ = lean_array_uget_borrowed(v_as_1331_, v_i_1333_);
                crate::leanh::lean_inc(v_snd_1340_);
                crate::leanh::lean_inc(v_a_1344_);
                v___x_1345_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_a_1344_, v_snd_1340_, v___y_1335_, v___y_1336_);
                if crate::leanh::lean_obj_tag(v___x_1345_) == 0 {
                    v_a_1346_ = crate::leanh::lean_ctor_get(v___x_1345_, 0);
                    v_isSharedCheck_1365_ = (!crate::leanh::lean_is_exclusive(v___x_1345_)) as u8;
                    if v_isSharedCheck_1365_ == 0 {
                        v___x_1348_ = v___x_1345_;
                        v_isShared_1349_ = v_isSharedCheck_1365_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1346_);
                        crate::leanh::lean_dec(v___x_1345_);
                        v___x_1348_ = crate::leanh::lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1365_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1342_);
                    crate::leanh::lean_dec(v_snd_1340_);
                    v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1345_, 0);
                    v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v___x_1345_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v___x_1368_ = v___x_1345_;
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1366_);
                        crate::leanh::lean_dec(v___x_1345_);
                        v___x_1368_ = crate::leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1346_) == 0 {
                    v___x_1350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1350_, 0, v_a_1346_);
                    if v_isShared_1343_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1350_);
                        v___x_1352_ = v___x_1342_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1340_);
                        v___x_1352_ = v_reuseFailAlloc_1356_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1348_);
                    crate::leanh::lean_dec(v_snd_1340_);
                    v_a_1357_ = crate::leanh::lean_ctor_get(v_a_1346_, 0);
                    crate::leanh::lean_inc(v_a_1357_);
                    crate::leanh::lean_dec_ref_known(v_a_1346_, 1);
                    v___x_1358_ = crate::leanh::lean_box(0);
                    if v_isShared_1343_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1342_, 1, v_a_1357_);
                        crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1358_);
                        v___x_1360_ = v___x_1342_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1364_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1358_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1357_);
                        v___x_1360_ = v_reuseFailAlloc_1364_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1352_);
                    v___x_1354_ = v___x_1348_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1354_;
            }
            5 => {
                v___x_1361_ = 1usize;
                v___x_1362_ = lean_usize_add(v_i_1333_, v___x_1361_);
                v_i_1333_ = v___x_1362_;
                v_b_1334_ = v___x_1360_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1369_ == 0 {
                    v___x_1371_ = v___x_1368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3___boxed(
    mut v_as_1376_: *mut crate::leanh::LeanObject,
    mut v_sz_1377_: *mut crate::leanh::LeanObject,
    mut v_i_1378_: *mut crate::leanh::LeanObject,
    mut v_b_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1383_: usize = 0;
    let mut v_i_boxed_1384_: usize = 0;
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1383_ = crate::leanh::lean_unbox_usize(v_sz_1377_);
    crate::leanh::lean_dec(v_sz_1377_);
    v_i_boxed_1384_ = crate::leanh::lean_unbox_usize(v_i_1378_);
    crate::leanh::lean_dec(v_i_1378_);
    v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_as_1376_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1379_, v___y_1380_, v___y_1381_);
    crate::leanh::lean_dec(v___y_1381_);
    crate::leanh::lean_dec_ref(v___y_1380_);
    crate::leanh::lean_dec_ref(v_as_1376_);
    return v_res_1385_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2___boxed(
    mut v_stx_1386_: *mut crate::leanh::LeanObject,
    mut v_b_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_1386_, v_b_1387_, v___y_1388_, v___y_1389_);
    crate::leanh::lean_dec(v___y_1389_);
    crate::leanh::lean_dec_ref(v___y_1388_);
    return v_res_1391_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(
    mut v_stx_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut v_unused_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1396_ = crate::leanh::lean_box(0);
                v___x_1397_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_1392_, v___x_1396_, v___y_1393_, v___y_1394_);
                if crate::leanh::lean_obj_tag(v___x_1397_) == 0 {
                    v_isSharedCheck_1404_ = (!crate::leanh::lean_is_exclusive(v___x_1397_)) as u8;
                    if v_isSharedCheck_1404_ == 0 {
                        v_unused_1405_ = crate::leanh::lean_ctor_get(v___x_1397_, 0);
                        crate::leanh::lean_dec(v_unused_1405_);
                        v___x_1399_ = v___x_1397_;
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1397_);
                        v___x_1399_ = crate::leanh::lean_box(0);
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1406_ = crate::leanh::lean_ctor_get(v___x_1397_, 0);
                    v_isSharedCheck_1413_ = (!crate::leanh::lean_is_exclusive(v___x_1397_)) as u8;
                    if v_isSharedCheck_1413_ == 0 {
                        v___x_1408_ = v___x_1397_;
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1406_);
                        crate::leanh::lean_dec(v___x_1397_);
                        v___x_1408_ = crate::leanh::lean_box(0);
                        v_isShared_1409_ = v_isSharedCheck_1413_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1399_, 0, v___x_1396_);
                    v___x_1402_ = v___x_1399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1396_);
                    v___x_1402_ = v_reuseFailAlloc_1403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1402_;
            }
            3 => {
                if v_isShared_1409_ == 0 {
                    v___x_1411_ = v___x_1408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed(
    mut v_stx_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ =
        l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(
            v_stx_1414_,
            v___y_1415_,
            v___y_1416_,
        );
    crate::leanh::lean_dec(v___y_1416_);
    crate::leanh::lean_dec_ref(v___y_1415_);
    return v_res_1418_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(
    mut v_msgData_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1458_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_1454_, v___y_1456_);
    return v___x_1458_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(v_msgData_1459_, v___y_1460_, v___y_1461_);
    crate::leanh::lean_dec(v___y_1461_);
    crate::leanh::lean_dec_ref(v___y_1460_);
    return v_res_1463_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn;
    v___x_1466_ = l_Lean_Elab_Command_addLinter(v___x_1465_);
    return v___x_1466_;
}
pub unsafe fn l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2____boxed(
    mut v_a_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
    return v_res_1468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_GlobalAttributeIn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_GlobalAttributeIn(
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
pub unsafe fn initialize_Lean_Linter_GlobalAttributeIn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_GlobalAttributeIn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_GlobalAttributeIn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_GlobalAttributeIn(builtin);
}
