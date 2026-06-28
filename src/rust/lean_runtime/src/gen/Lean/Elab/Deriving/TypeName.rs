// Lean compiler output
// Module: Lean.Elab.Deriving.TypeName
// Imports: Lean.Elab.Deriving.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_mkCIdent, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_levelParams;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_getCurrMacroScope___redArg,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_withFreshMacroScope___redArg,
    l_Lean_Elab_Command_withScope___redArg,
};
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, l_Lean_Elab_registerDerivingHandler,
    runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_push, lean_mk_empty_array_with_capacity,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 97, 114, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 108, 97, 115, 115, 68, 101, 102, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value) as *mut LeanObject,9767581756212181691 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value) as *mut LeanObject,12998338075612071922 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value) as *mut LeanObject,5229394285883816413 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 112, 97, 113, 117, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 115, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value) as *mut LeanObject,6605161548626312362 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 115, 97, 102, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value) as *mut LeanObject,10398938568477941839 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value) as *mut LeanObject,9789339221525904376 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value) as *mut LeanObject,1827444229220621555 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 73, 109, 112, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value) as *mut LeanObject,385442998356221160 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value) as *mut LeanObject,5473625859156281626 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 121, 112, 101, 78, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value) as *mut LeanObject,574021635941469103 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value) as *mut LeanObject,13290931718435096973 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value) as *mut LeanObject,13585030837571646948 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value) as *mut LeanObject,14183307858573822893 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value) as *mut LeanObject,12500803453736965855 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [32, 104, 97, 115, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(
    mut v_o_1020_: *mut LeanObject,
    mut v_k_1021_: *mut LeanObject,
    mut v_v_1022_: u8,
) -> *mut LeanObject {
    let mut v_map_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1024_: u8 = 0;
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1023_ = lean_ctor_get(v_o_1020_, 0);
                v_hasTrace_1024_ = lean_ctor_get_uint8(
                    v_o_1020_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1038_ = (!lean_is_exclusive(v_o_1020_)) as u8;
                if v_isSharedCheck_1038_ == 0 {
                    v___x_1026_ = v_o_1020_;
                    v_isShared_1027_ = v_isSharedCheck_1038_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_1023_);
                    lean_dec(v_o_1020_);
                    v___x_1026_ = lean_box(0);
                    v_isShared_1027_ = v_isSharedCheck_1038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1028_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_1028_, 0 as u32, v_v_1022_);
                lean_inc(v_k_1021_);
                v___x_1029_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1021_, v___x_1028_, v_map_1023_);
                if v_hasTrace_1024_ == 0 {
                    v___x_1030_ = l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1;
                    v___x_1031_ = l_Lean_Name_isPrefixOf(v___x_1030_, v_k_1021_);
                    lean_dec(v_k_1021_);
                    if v_isShared_1027_ == 0 {
                        lean_ctor_set(v___x_1026_, 0, v___x_1029_);
                        v___x_1033_ = v___x_1026_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
                        v___x_1033_ = v_reuseFailAlloc_1034_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1021_);
                    if v_isShared_1027_ == 0 {
                        lean_ctor_set(v___x_1026_, 0, v___x_1029_);
                        v___x_1036_ = v___x_1026_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1029_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1037_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_1024_,
                        );
                        v___x_1036_ = v_reuseFailAlloc_1037_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1033_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1031_,
                );
                return v___x_1033_;
            }
            3 => {
                return v___x_1036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___boxed(
    mut v_o_1039_: *mut LeanObject,
    mut v_k_1040_: *mut LeanObject,
    mut v_v_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1042_: u8 = 0;
    let mut v_res_1043_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1042_ = (lean_unbox(v_v_1041_) as u8);
    v_res_1043_ = l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(v_o_1039_, v_k_1040_, v_v_boxed_1042_);
    return v_res_1043_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(
    mut v___y_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = lean_st_ref_get(v___y_1044_);
    v_env_1047_ = lean_ctor_get(v___x_1046_, 0);
    lean_inc_ref(v_env_1047_);
    lean_dec(v___x_1046_);
    v___x_1048_ = l_Lean_Environment_header(v_env_1047_);
    lean_dec_ref(v_env_1047_);
    v_mainModule_1049_ = lean_ctor_get(v___x_1048_, 0);
    lean_inc(v_mainModule_1049_);
    lean_dec_ref(v___x_1048_);
    v___x_1050_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1050_, 0, v_mainModule_1049_);
    return v___x_1050_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg___boxed(
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1053_: *mut LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_1051_);
    lean_dec(v___y_1051_);
    return v_res_1053_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_1055_);
    return v___x_1057_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___boxed(
    mut v___y_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1061_: *mut LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(v___y_1058_, v___y_1059_);
    lean_dec(v___y_1059_);
    lean_dec_ref(v___y_1058_);
    return v_res_1061_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0(
    mut v_scope_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_header_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelNames_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varDecls_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varUIds_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includedVars_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_1077_: u8 = 0;
    let mut v_isPublic_1078_: u8 = 0;
    let mut v_isMeta_1079_: u8 = 0;
    let mut v_attrs_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1083_: u8 = 0;
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_1068_ = lean_ctor_get(v_scope_1067_, 0);
                v_opts_1069_ = lean_ctor_get(v_scope_1067_, 1);
                v_currNamespace_1070_ = lean_ctor_get(v_scope_1067_, 2);
                v_openDecls_1071_ = lean_ctor_get(v_scope_1067_, 3);
                v_levelNames_1072_ = lean_ctor_get(v_scope_1067_, 4);
                v_varDecls_1073_ = lean_ctor_get(v_scope_1067_, 5);
                v_varUIds_1074_ = lean_ctor_get(v_scope_1067_, 6);
                v_includedVars_1075_ = lean_ctor_get(v_scope_1067_, 7);
                v_omittedVars_1076_ = lean_ctor_get(v_scope_1067_, 8);
                v_isNoncomputable_1077_ = lean_ctor_get_uint8(
                    v_scope_1067_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isPublic_1078_ = lean_ctor_get_uint8(
                    v_scope_1067_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_1079_ = lean_ctor_get_uint8(
                    v_scope_1067_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_1080_ = lean_ctor_get(v_scope_1067_, 9);
                v_isSharedCheck_1090_ = (!lean_is_exclusive(v_scope_1067_)) as u8;
                if v_isSharedCheck_1090_ == 0 {
                    v___x_1082_ = v_scope_1067_;
                    v_isShared_1083_ = v_isSharedCheck_1090_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_attrs_1080_);
                    lean_inc(v_omittedVars_1076_);
                    lean_inc(v_includedVars_1075_);
                    lean_inc(v_varUIds_1074_);
                    lean_inc(v_varDecls_1073_);
                    lean_inc(v_levelNames_1072_);
                    lean_inc(v_openDecls_1071_);
                    lean_inc(v_currNamespace_1070_);
                    lean_inc(v_opts_1069_);
                    lean_inc(v_header_1068_);
                    lean_dec(v_scope_1067_);
                    v___x_1082_ = lean_box(0);
                    v_isShared_1083_ = v_isSharedCheck_1090_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2;
                v___x_1085_ = 0;
                v___x_1086_ = l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(v_opts_1069_, v___x_1084_, v___x_1085_);
                if v_isShared_1083_ == 0 {
                    lean_ctor_set(v___x_1082_, 1, v___x_1086_);
                    v___x_1088_ = v___x_1082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 10, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_header_1068_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_currNamespace_1070_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_openDecls_1071_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_levelNames_1072_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_varDecls_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_varUIds_1074_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_includedVars_1075_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 8, v_omittedVars_1076_);
                    lean_ctor_set(v_reuseFailAlloc_1089_, 9, v_attrs_1080_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1089_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_isNoncomputable_1077_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1089_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                        v_isPublic_1078_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1089_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                        v_isMeta_1079_,
                    );
                    v___x_1088_ = v_reuseFailAlloc_1089_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2(
    mut v___f_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1095_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(
                    v___f_1091_,
                    v___y_1092_,
                    v___y_1093_,
                );
                if lean_obj_tag(v___x_1095_) == 0 {
                    v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
                    lean_inc(v_a_1096_);
                    lean_dec_ref_known(v___x_1095_, 1);
                    v___x_1097_ =
                        l_Lean_Elab_Command_elabCommand(v_a_1096_, v___y_1092_, v___y_1093_);
                    return v___x_1097_;
                } else {
                    v_a_1098_ = lean_ctor_get(v___x_1095_, 0);
                    v_isSharedCheck_1105_ = (!lean_is_exclusive(v___x_1095_)) as u8;
                    if v_isSharedCheck_1105_ == 0 {
                        v___x_1100_ = v___x_1095_;
                        v_isShared_1101_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1098_);
                        lean_dec(v___x_1095_);
                        v___x_1100_ = lean_box(0);
                        v_isShared_1101_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1101_ == 0 {
                    v___x_1103_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
                    v___x_1103_ = v_reuseFailAlloc_1104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed(
    mut v___f_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2(v___f_1106_, v___y_1107_, v___y_1108_);
    lean_dec(v___y_1108_);
    lean_dec_ref(v___y_1107_);
    return v_res_1110_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9()
-> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8;
    v___x_1121_ = l_String_toRawSubstring_x27(v___x_1120_);
    return v___x_1121_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14()
-> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13;
    v___x_1128_ = l_String_toRawSubstring_x27(v___x_1127_);
    return v___x_1128_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27()
-> *mut LeanObject {
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Array_mkArray0(lean_box(0));
    return v___x_1151_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36()
-> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35;
    v___x_1173_ = l_String_toRawSubstring_x27(v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47()
-> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46;
    v___x_1198_ = l_String_toRawSubstring_x27(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63()
-> *mut LeanObject {
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62;
    v___x_1235_ = l_String_toRawSubstring_x27(v___x_1234_);
    return v___x_1235_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1(
    mut v_a_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v_quotContext_x3f_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut v_val_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_a_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1256_ = l_Lean_Elab_Command_getRef___redArg(v___y_1253_);
                if lean_obj_tag(v___x_1256_) == 0 {
                    v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
                    lean_inc(v_a_1257_);
                    lean_dec_ref_known(v___x_1256_, 1);
                    v___x_1258_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1253_);
                    if lean_obj_tag(v___x_1258_) == 0 {
                        v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
                        v_isSharedCheck_1435_ = (!lean_is_exclusive(v___x_1258_)) as u8;
                        if v_isSharedCheck_1435_ == 0 {
                            v___x_1261_ = v___x_1258_;
                            v_isShared_1262_ = v_isSharedCheck_1435_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1259_);
                            lean_dec(v___x_1258_);
                            v___x_1261_ = lean_box(0);
                            v_isShared_1262_ = v_isSharedCheck_1435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1257_);
                        lean_dec_ref(v___y_1253_);
                        lean_dec(v_a_1252_);
                        v_a_1436_ = lean_ctor_get(v___x_1258_, 0);
                        v_isSharedCheck_1443_ = (!lean_is_exclusive(v___x_1258_)) as u8;
                        if v_isSharedCheck_1443_ == 0 {
                            v___x_1438_ = v___x_1258_;
                            v_isShared_1439_ = v_isSharedCheck_1443_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1436_);
                            lean_dec(v___x_1258_);
                            v___x_1438_ = lean_box(0);
                            v_isShared_1439_ = v_isSharedCheck_1443_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_1253_);
                    lean_dec(v_a_1252_);
                    v_a_1444_ = lean_ctor_get(v___x_1256_, 0);
                    v_isSharedCheck_1451_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                    if v_isSharedCheck_1451_ == 0 {
                        v___x_1446_ = v___x_1256_;
                        v_isShared_1447_ = v_isSharedCheck_1451_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1444_);
                        lean_dec(v___x_1256_);
                        v___x_1446_ = lean_box(0);
                        v_isShared_1447_ = v_isSharedCheck_1451_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_x3f_1263_ = lean_ctor_get(v___y_1253_, 5);
                lean_inc(v_quotContext_x3f_1263_);
                lean_dec_ref(v___y_1253_);
                v___x_1264_ = 0;
                v___x_1265_ = l_Lean_SourceInfo_fromRef(v_a_1257_, v___x_1264_);
                lean_dec(v_a_1257_);
                if lean_obj_tag(v_quotContext_x3f_1263_) == 0 {
                    v___x_1424_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_1254_);
                    if lean_obj_tag(v___x_1424_) == 0 {
                        v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
                        lean_inc(v_a_1425_);
                        lean_dec_ref_known(v___x_1424_, 1);
                        v_a_1350_ = v_a_1425_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_1265_);
                        lean_del_object(v___x_1261_);
                        lean_dec(v_a_1259_);
                        lean_dec(v_a_1252_);
                        v_a_1426_ = lean_ctor_get(v___x_1424_, 0);
                        v_isSharedCheck_1433_ = (!lean_is_exclusive(v___x_1424_)) as u8;
                        if v_isSharedCheck_1433_ == 0 {
                            v___x_1428_ = v___x_1424_;
                            v_isShared_1429_ = v_isSharedCheck_1433_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1426_);
                            lean_dec(v___x_1424_);
                            v___x_1428_ = lean_box(0);
                            v_isShared_1429_ = v_isSharedCheck_1433_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_val_1434_ = lean_ctor_get(v_quotContext_x3f_1263_, 0);
                    lean_inc(v_val_1434_);
                    lean_dec_ref_known(v_quotContext_x3f_1263_, 1);
                    v_a_1350_ = v_val_1434_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v___y_1282_, 4);
                lean_inc_n(v___x_1265_, 28);
                v___x_1291_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1282_, v___y_1277_, v___y_1290_);
                v___x_1292_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1268_, v___y_1283_, v___x_1291_);
                v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0;
                v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1;
                lean_inc_ref_n(v___y_1284_, 8);
                lean_inc_ref_n(v___y_1276_, 8);
                v___x_1295_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___x_1293_, v___x_1294_);
                lean_inc_n(v___y_1273_, 23);
                v___x_1296_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1295_, v___y_1273_, v___y_1273_);
                lean_inc(v___x_1296_);
                lean_inc(v___y_1286_);
                lean_inc_n(v___y_1271_, 2);
                v___x_1297_ = l_Lean_Syntax_node4(
                    v___x_1265_,
                    v___y_1271_,
                    v___y_1286_,
                    v___x_1292_,
                    v___x_1296_,
                    v___y_1273_,
                );
                lean_inc(v___y_1279_);
                v___x_1298_ = l_Lean_Syntax_node5(
                    v___x_1265_,
                    v___y_1279_,
                    v___y_1280_,
                    v___y_1269_,
                    v___y_1281_,
                    v___x_1297_,
                    v___y_1273_,
                );
                lean_inc_n(v___y_1267_, 3);
                v___x_1299_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1267_, v___y_1285_, v___x_1298_);
                v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2;
                lean_inc_ref_n(v___y_1288_, 3);
                v___x_1301_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1288_, v___x_1300_);
                v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3;
                v___x_1303_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1303_, 0, v___x_1265_);
                lean_ctor_set(v___x_1303_, 1, v___x_1302_);
                v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4;
                v___x_1305_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1288_, v___x_1304_);
                v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5;
                v___x_1307_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1288_, v___x_1306_);
                v___x_1308_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1307_, v___y_1273_);
                v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6;
                v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7;
                v___x_1311_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___x_1309_, v___x_1310_);
                v___x_1312_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9);
                v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10;
                lean_inc(v_a_1259_);
                lean_inc(v___y_1278_);
                v___x_1314_ = l_Lean_addMacroScope(v___y_1278_, v___x_1313_, v_a_1259_);
                lean_inc(v___y_1270_);
                v___x_1315_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1315_, 0, v___x_1265_);
                lean_ctor_set(v___x_1315_, 1, v___x_1312_);
                lean_ctor_set(v___x_1315_, 2, v___x_1314_);
                lean_ctor_set(v___x_1315_, 3, v___y_1270_);
                v___x_1316_ = l_Lean_Syntax_node1(v___x_1265_, v___y_1282_, v___y_1274_);
                v___x_1317_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1311_, v___x_1315_, v___x_1316_);
                lean_inc(v___x_1308_);
                v___x_1318_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1305_, v___x_1308_, v___x_1317_);
                v___x_1319_ = l_Lean_Syntax_node1(v___x_1265_, v___y_1282_, v___x_1318_);
                v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11;
                v___x_1321_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1321_, 0, v___x_1265_);
                lean_ctor_set(v___x_1321_, 1, v___x_1320_);
                v___x_1322_ = l_Lean_Syntax_node3(
                    v___x_1265_,
                    v___x_1301_,
                    v___x_1303_,
                    v___x_1319_,
                    v___x_1321_,
                );
                v___x_1323_ = l_Lean_Syntax_node1(v___x_1265_, v___y_1282_, v___x_1322_);
                lean_inc(v___y_1287_);
                v___x_1324_ = l_Lean_Syntax_node7(
                    v___x_1265_,
                    v___y_1287_,
                    v___y_1273_,
                    v___x_1323_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                );
                v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12;
                lean_inc_ref_n(v___y_1272_, 3);
                v___x_1326_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1272_, v___x_1325_);
                v___x_1327_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1327_, 0, v___x_1265_);
                lean_ctor_set(v___x_1327_, 1, v___x_1325_);
                v___x_1328_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14);
                v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15;
                v___x_1330_ = l_Lean_addMacroScope(v___y_1278_, v___x_1329_, v_a_1259_);
                v___x_1331_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1331_, 0, v___x_1265_);
                lean_ctor_set(v___x_1331_, 1, v___x_1328_);
                lean_ctor_set(v___x_1331_, 2, v___x_1330_);
                lean_ctor_set(v___x_1331_, 3, v___y_1270_);
                lean_inc_ref(v___x_1331_);
                v___x_1332_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1275_, v___x_1331_, v___y_1273_);
                v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16;
                v___x_1334_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1272_, v___x_1333_);
                v___x_1335_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1334_, v___y_1273_, v___y_1289_);
                lean_inc(v___x_1335_);
                v___x_1336_ = l_Lean_Syntax_node4(
                    v___x_1265_,
                    v___x_1326_,
                    v___x_1327_,
                    v___x_1332_,
                    v___x_1335_,
                    v___y_1273_,
                );
                v___x_1337_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1267_, v___x_1324_, v___x_1336_);
                v___x_1338_ = l_Lean_Syntax_node7(
                    v___x_1265_,
                    v___y_1287_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                    v___y_1273_,
                );
                v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17;
                v___x_1340_ =
                    l_Lean_Name_mkStr4(v___y_1276_, v___y_1284_, v___y_1272_, v___x_1339_);
                v___x_1341_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1341_, 0, v___x_1265_);
                lean_ctor_set(v___x_1341_, 1, v___x_1339_);
                v___x_1342_ = l_Lean_Syntax_node4(
                    v___x_1265_,
                    v___y_1271_,
                    v___y_1286_,
                    v___x_1331_,
                    v___x_1296_,
                    v___y_1273_,
                );
                v___x_1343_ = l_Lean_Syntax_node6(
                    v___x_1265_,
                    v___x_1340_,
                    v___x_1308_,
                    v___x_1341_,
                    v___y_1273_,
                    v___y_1273_,
                    v___x_1335_,
                    v___x_1342_,
                );
                v___x_1344_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___y_1267_, v___x_1338_, v___x_1343_);
                v___x_1345_ = l_Lean_Syntax_node3(
                    v___x_1265_,
                    v___y_1282_,
                    v___x_1299_,
                    v___x_1337_,
                    v___x_1344_,
                );
                if v_isShared_1262_ == 0 {
                    lean_ctor_set(v___x_1261_, 0, v___x_1345_);
                    v___x_1347_ = v___x_1261_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1347_;
            }
            4 => {
                v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19;
                v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20;
                v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21;
                v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22;
                v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24;
                v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26;
                v___x_1357_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27);
                lean_inc_n(v___x_1265_, 23);
                v___x_1358_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1358_, 0, v___x_1265_);
                lean_ctor_set(v___x_1358_, 1, v___x_1351_);
                lean_ctor_set(v___x_1358_, 2, v___x_1357_);
                v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28;
                v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29;
                v___x_1361_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1361_, 0, v___x_1265_);
                lean_ctor_set(v___x_1361_, 1, v___x_1359_);
                v___x_1362_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1360_, v___x_1361_);
                v___x_1363_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1351_, v___x_1362_);
                lean_inc_ref_n(v___x_1358_, 8);
                v___x_1364_ = l_Lean_Syntax_node7(
                    v___x_1265_,
                    v___x_1356_,
                    v___x_1358_,
                    v___x_1358_,
                    v___x_1358_,
                    v___x_1358_,
                    v___x_1358_,
                    v___x_1363_,
                    v___x_1358_,
                );
                v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31;
                v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32;
                v___x_1367_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1367_, 0, v___x_1265_);
                lean_ctor_set(v___x_1367_, 1, v___x_1366_);
                v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34;
                v___x_1369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36);
                v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37;
                lean_inc_n(v_a_1259_, 3);
                lean_inc_n(v_a_1350_, 3);
                v___x_1371_ = l_Lean_addMacroScope(v_a_1350_, v___x_1370_, v_a_1259_);
                v___x_1372_ = lean_box(0);
                v___x_1373_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1373_, 0, v___x_1265_);
                lean_ctor_set(v___x_1373_, 1, v___x_1369_);
                lean_ctor_set(v___x_1373_, 2, v___x_1371_);
                lean_ctor_set(v___x_1373_, 3, v___x_1372_);
                lean_inc_ref(v___x_1373_);
                v___x_1374_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1368_, v___x_1373_, v___x_1358_);
                v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39;
                v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40;
                v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42;
                v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43;
                v___x_1379_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1379_, 0, v___x_1265_);
                lean_ctor_set(v___x_1379_, 1, v___x_1378_);
                v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45;
                v___x_1381_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47);
                v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48;
                v___x_1383_ = l_Lean_addMacroScope(v_a_1350_, v___x_1382_, v_a_1259_);
                v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52;
                v___x_1385_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1385_, 0, v___x_1265_);
                lean_ctor_set(v___x_1385_, 1, v___x_1381_);
                lean_ctor_set(v___x_1385_, 2, v___x_1383_);
                lean_ctor_set(v___x_1385_, 3, v___x_1384_);
                v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54;
                v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55;
                v___x_1388_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1388_, 0, v___x_1265_);
                lean_ctor_set(v___x_1388_, 1, v___x_1387_);
                lean_inc_n(v_a_1252_, 2);
                v___x_1389_ = l_Lean_mkCIdent(v_a_1252_);
                v___x_1390_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1386_, v___x_1388_, v___x_1389_);
                v___x_1391_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1351_, v___x_1390_);
                v___x_1392_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1380_, v___x_1385_, v___x_1391_);
                v___x_1393_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1377_, v___x_1379_, v___x_1392_);
                lean_inc(v___x_1393_);
                v___x_1394_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1351_, v___x_1393_);
                v___x_1395_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1375_, v___x_1358_, v___x_1394_);
                v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57;
                v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58;
                v___x_1398_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1398_, 0, v___x_1265_);
                lean_ctor_set(v___x_1398_, 1, v___x_1397_);
                v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60;
                v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61;
                v___x_1401_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1401_, 0, v___x_1265_);
                lean_ctor_set(v___x_1401_, 1, v___x_1400_);
                v___x_1402_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63);
                v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64;
                v___x_1404_ = l_Lean_addMacroScope(v_a_1350_, v___x_1403_, v_a_1259_);
                v___x_1405_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1405_, 0, v___x_1265_);
                lean_ctor_set(v___x_1405_, 1, v___x_1402_);
                lean_ctor_set(v___x_1405_, 2, v___x_1404_);
                lean_ctor_set(v___x_1405_, 3, v___x_1372_);
                v___x_1406_ =
                    l_Lean_Syntax_node2(v___x_1265_, v___x_1399_, v___x_1401_, v___x_1405_);
                v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66;
                v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67;
                v___x_1409_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1409_, 0, v___x_1265_);
                lean_ctor_set(v___x_1409_, 1, v___x_1408_);
                v___x_1410_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1407_, v___x_1409_);
                v___x_1411_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_1372_,
                    v_a_1252_,
                );
                if lean_obj_tag(v___x_1411_) == 0 {
                    v___x_1412_ = l_Lean_quoteNameMk(v_a_1252_);
                    v___y_1267_ = v___x_1355_;
                    v___y_1268_ = v___x_1380_;
                    v___y_1269_ = v___x_1374_;
                    v___y_1270_ = v___x_1372_;
                    v___y_1271_ = v___x_1396_;
                    v___y_1272_ = v___x_1354_;
                    v___y_1273_ = v___x_1358_;
                    v___y_1274_ = v___x_1373_;
                    v___y_1275_ = v___x_1368_;
                    v___y_1276_ = v___x_1352_;
                    v___y_1277_ = v___x_1410_;
                    v___y_1278_ = v_a_1350_;
                    v___y_1279_ = v___x_1365_;
                    v___y_1280_ = v___x_1367_;
                    v___y_1281_ = v___x_1395_;
                    v___y_1282_ = v___x_1351_;
                    v___y_1283_ = v___x_1406_;
                    v___y_1284_ = v___x_1353_;
                    v___y_1285_ = v___x_1364_;
                    v___y_1286_ = v___x_1398_;
                    v___y_1287_ = v___x_1356_;
                    v___y_1288_ = v___x_1376_;
                    v___y_1289_ = v___x_1393_;
                    v___y_1290_ = v___x_1412_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_a_1252_);
                    v_val_1413_ = lean_ctor_get(v___x_1411_, 0);
                    lean_inc(v_val_1413_);
                    lean_dec_ref_known(v___x_1411_, 1);
                    v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69;
                    v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70;
                    v___x_1416_ = lean_string_intercalate(v___x_1400_, v_val_1413_);
                    v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
                    lean_dec_ref(v___x_1416_);
                    v___x_1418_ = lean_box(2);
                    v___x_1419_ = l_Lean_Syntax_mkNameLit(v___x_1417_, v___x_1418_);
                    v___x_1420_ = lean_unsigned_to_nat(1);
                    v___x_1421_ = lean_mk_empty_array_with_capacity(v___x_1420_);
                    v___x_1422_ = lean_array_push(v___x_1421_, v___x_1419_);
                    v___x_1423_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1423_, 0, v___x_1418_);
                    lean_ctor_set(v___x_1423_, 1, v___x_1414_);
                    lean_ctor_set(v___x_1423_, 2, v___x_1422_);
                    v___y_1267_ = v___x_1355_;
                    v___y_1268_ = v___x_1380_;
                    v___y_1269_ = v___x_1374_;
                    v___y_1270_ = v___x_1372_;
                    v___y_1271_ = v___x_1396_;
                    v___y_1272_ = v___x_1354_;
                    v___y_1273_ = v___x_1358_;
                    v___y_1274_ = v___x_1373_;
                    v___y_1275_ = v___x_1368_;
                    v___y_1276_ = v___x_1352_;
                    v___y_1277_ = v___x_1410_;
                    v___y_1278_ = v_a_1350_;
                    v___y_1279_ = v___x_1365_;
                    v___y_1280_ = v___x_1367_;
                    v___y_1281_ = v___x_1395_;
                    v___y_1282_ = v___x_1351_;
                    v___y_1283_ = v___x_1406_;
                    v___y_1284_ = v___x_1353_;
                    v___y_1285_ = v___x_1364_;
                    v___y_1286_ = v___x_1398_;
                    v___y_1287_ = v___x_1356_;
                    v___y_1288_ = v___x_1376_;
                    v___y_1289_ = v___x_1393_;
                    v___y_1290_ = v___x_1423_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_1429_ == 0 {
                    v___x_1431_ = v___x_1428_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
                    v___x_1431_ = v_reuseFailAlloc_1432_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1431_;
            }
            7 => {
                if v_isShared_1439_ == 0 {
                    v___x_1441_ = v___x_1438_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1441_;
            }
            9 => {
                if v_isShared_1447_ == 0 {
                    v___x_1449_ = v___x_1446_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
                    v___x_1449_ = v_reuseFailAlloc_1450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed(
    mut v_a_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1(v_a_1452_, v___y_1453_, v___y_1454_);
    lean_dec(v___y_1454_);
    return v_res_1456_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1457_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0);
    v___x_1459_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1459_, 0, v___x_1458_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1);
    v___x_1461_ = lean_unsigned_to_nat(0);
    v___x_1462_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1462_, 0, v___x_1461_);
    lean_ctor_set(v___x_1462_, 1, v___x_1461_);
    lean_ctor_set(v___x_1462_, 2, v___x_1461_);
    lean_ctor_set(v___x_1462_, 3, v___x_1461_);
    lean_ctor_set(v___x_1462_, 4, v___x_1460_);
    lean_ctor_set(v___x_1462_, 5, v___x_1460_);
    lean_ctor_set(v___x_1462_, 6, v___x_1460_);
    lean_ctor_set(v___x_1462_, 7, v___x_1460_);
    lean_ctor_set(v___x_1462_, 8, v___x_1460_);
    lean_ctor_set(v___x_1462_, 9, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = lean_unsigned_to_nat(32);
    v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
    v___x_1465_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1465_, 0, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1466_: usize = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    v___x_1466_ = 5usize;
    v___x_1467_ = lean_unsigned_to_nat(0);
    v___x_1468_ = lean_unsigned_to_nat(32);
    v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
    v___x_1470_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3);
    v___x_1471_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1471_, 0, v___x_1470_);
    lean_ctor_set(v___x_1471_, 1, v___x_1469_);
    lean_ctor_set(v___x_1471_, 2, v___x_1467_);
    lean_ctor_set(v___x_1471_, 3, v___x_1467_);
    lean_ctor_set_usize(v___x_1471_, 4, v___x_1466_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_1472_ = lean_box(1);
    v___x_1473_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4);
    v___x_1474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1);
    v___x_1475_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1475_, 0, v___x_1474_);
    lean_ctor_set(v___x_1475_, 1, v___x_1473_);
    lean_ctor_set(v___x_1475_, 2, v___x_1472_);
    return v___x_1475_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(
    mut v_msgData_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = lean_st_ref_get(v___y_1477_);
    v_env_1480_ = lean_ctor_get(v___x_1479_, 0);
    lean_inc_ref(v_env_1480_);
    lean_dec(v___x_1479_);
    v___x_1481_ = lean_st_ref_get(v___y_1477_);
    v_scopes_1482_ = lean_ctor_get(v___x_1481_, 2);
    lean_inc(v_scopes_1482_);
    lean_dec(v___x_1481_);
    v___x_1483_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1484_ = l_List_head_x21___redArg(v___x_1483_, v_scopes_1482_);
    lean_dec(v_scopes_1482_);
    v_opts_1485_ = lean_ctor_get(v___x_1484_, 1);
    lean_inc_ref(v_opts_1485_);
    lean_dec(v___x_1484_);
    v___x_1486_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
    v___x_1487_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
    v___x_1488_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1488_, 0, v_env_1480_);
    lean_ctor_set(v___x_1488_, 1, v___x_1486_);
    lean_ctor_set(v___x_1488_, 2, v___x_1487_);
    lean_ctor_set(v___x_1488_, 3, v_opts_1485_);
    v___x_1489_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    lean_ctor_set(v___x_1489_, 1, v_msgData_1476_);
    v___x_1490_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1490_, 0, v___x_1489_);
    return v___x_1490_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___boxed(
    mut v_msgData_1491_: *mut LeanObject,
    mut v___y_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_1491_, v___y_1492_);
    lean_dec(v___y_1492_);
    return v_res_1494_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(
    mut v_opts_1495_: *mut LeanObject,
    mut v_opt_1496_: *mut LeanObject,
) -> u8 {
    let mut v_name_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v_name_1497_ = lean_ctor_get(v_opt_1496_, 0);
    v_defValue_1498_ = lean_ctor_get(v_opt_1496_, 1);
    v_map_1499_ = lean_ctor_get(v_opts_1495_, 0);
    v___x_1500_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1499_,
            v_name_1497_,
        );
    if lean_obj_tag(v___x_1500_) == 0 {
        let mut v___x_1501_: u8 = 0;
        v___x_1501_ = (lean_unbox(v_defValue_1498_) as u8);
        return v___x_1501_;
    } else {
        let mut v_val_1502_: *mut LeanObject = core::ptr::null_mut();
        v_val_1502_ = lean_ctor_get(v___x_1500_, 0);
        lean_inc(v_val_1502_);
        lean_dec_ref_known(v___x_1500_, 1);
        if lean_obj_tag(v_val_1502_) == 1 {
            let mut v_v_1503_: u8 = 0;
            v_v_1503_ = lean_ctor_get_uint8(v_val_1502_, 0 as u32);
            lean_dec_ref_known(v_val_1502_, 0);
            return v_v_1503_;
        } else {
            let mut v___x_1504_: u8 = 0;
            lean_dec(v_val_1502_);
            v___x_1504_ = (lean_unbox(v_defValue_1498_) as u8);
            return v___x_1504_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7___boxed(
    mut v_opts_1505_: *mut LeanObject,
    mut v_opt_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1507_: u8 = 0;
    let mut v_r_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1507_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_1505_, v_opt_1506_);
    lean_dec_ref(v_opt_1506_);
    lean_dec_ref(v_opts_1505_);
    v_r_1508_ = lean_box((v_res_1507_) as usize);
    return v_r_1508_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0()
-> *mut LeanObject {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    v___x_1509_ = lean_box(1);
    v___x_1510_ = l_Lean_MessageData_ofFormat(v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3()
-> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2;
    v___x_1515_ = l_Lean_MessageData_ofFormat(v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(
    mut v_x_1516_: *mut LeanObject,
    mut v_x_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v_before_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v_unused_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1517_) == 0 {
                    return v_x_1516_;
                } else {
                    v_head_1518_ = lean_ctor_get(v_x_1517_, 0);
                    v_tail_1519_ = lean_ctor_get(v_x_1517_, 1);
                    v_isSharedCheck_1541_ = (!lean_is_exclusive(v_x_1517_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1521_ = v_x_1517_;
                        v_isShared_1522_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1519_);
                        lean_inc(v_head_1518_);
                        lean_dec(v_x_1517_);
                        v___x_1521_ = lean_box(0);
                        v_isShared_1522_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1523_ = lean_ctor_get(v_head_1518_, 0);
                v_isSharedCheck_1539_ = (!lean_is_exclusive(v_head_1518_)) as u8;
                if v_isSharedCheck_1539_ == 0 {
                    v_unused_1540_ = lean_ctor_get(v_head_1518_, 1);
                    lean_dec(v_unused_1540_);
                    v___x_1525_ = v_head_1518_;
                    v_isShared_1526_ = v_isSharedCheck_1539_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1523_);
                    lean_dec(v_head_1518_);
                    v___x_1525_ = lean_box(0);
                    v_isShared_1526_ = v_isSharedCheck_1539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1527_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
                if v_isShared_1526_ == 0 {
                    lean_ctor_set_tag(v___x_1525_, 7);
                    lean_ctor_set(v___x_1525_, 1, v___x_1527_);
                    lean_ctor_set(v___x_1525_, 0, v_x_1516_);
                    v___x_1529_ = v___x_1525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_x_1516_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1530_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3);
                if v_isShared_1522_ == 0 {
                    lean_ctor_set_tag(v___x_1521_, 7);
                    lean_ctor_set(v___x_1521_, 1, v___x_1530_);
                    lean_ctor_set(v___x_1521_, 0, v___x_1529_);
                    v___x_1532_ = v___x_1521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1529_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1530_);
                    v___x_1532_ = v_reuseFailAlloc_1537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1533_ = l_Lean_MessageData_ofSyntax(v_before_1523_);
                v___x_1534_ = l_Lean_indentD(v___x_1533_);
                v___x_1535_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1535_, 0, v___x_1532_);
                lean_ctor_set(v___x_1535_, 1, v___x_1534_);
                v_x_1516_ = v___x_1535_;
                v_x_1517_ = v_tail_1519_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1545_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1;
    v___x_1546_ = l_Lean_MessageData_ofFormat(v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(
    mut v_msgData_1547_: *mut LeanObject,
    mut v_macroStack_1548_: *mut LeanObject,
    mut v___y_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1551_ = lean_st_ref_get(v___y_1549_);
                v_scopes_1552_ = lean_ctor_get(v___x_1551_, 2);
                lean_inc(v_scopes_1552_);
                lean_dec(v___x_1551_);
                v___x_1553_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1554_ = l_List_head_x21___redArg(v___x_1553_, v_scopes_1552_);
                lean_dec(v_scopes_1552_);
                v_opts_1555_ = lean_ctor_get(v___x_1554_, 1);
                lean_inc_ref(v_opts_1555_);
                lean_dec(v___x_1554_);
                v___x_1556_ = l_Lean_Elab_pp_macroStack;
                v___x_1557_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_1555_, v___x_1556_);
                lean_dec_ref(v_opts_1555_);
                if v___x_1557_ == 0 {
                    lean_dec(v_macroStack_1548_);
                    v___x_1558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1558_, 0, v_msgData_1547_);
                    return v___x_1558_;
                } else {
                    if lean_obj_tag(v_macroStack_1548_) == 0 {
                        v___x_1559_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1559_, 0, v_msgData_1547_);
                        return v___x_1559_;
                    } else {
                        v_head_1560_ = lean_ctor_get(v_macroStack_1548_, 0);
                        lean_inc(v_head_1560_);
                        v_after_1561_ = lean_ctor_get(v_head_1560_, 1);
                        v_isSharedCheck_1576_ = (!lean_is_exclusive(v_head_1560_)) as u8;
                        if v_isSharedCheck_1576_ == 0 {
                            v_unused_1577_ = lean_ctor_get(v_head_1560_, 0);
                            lean_dec(v_unused_1577_);
                            v___x_1563_ = v_head_1560_;
                            v_isShared_1564_ = v_isSharedCheck_1576_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_1561_);
                            lean_dec(v_head_1560_);
                            v___x_1563_ = lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1576_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1565_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
                if v_isShared_1564_ == 0 {
                    lean_ctor_set_tag(v___x_1563_, 7);
                    lean_ctor_set(v___x_1563_, 1, v___x_1565_);
                    lean_ctor_set(v___x_1563_, 0, v_msgData_1547_);
                    v___x_1567_ = v___x_1563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_msgData_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1565_);
                    v___x_1567_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1568_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2);
                v___x_1569_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1569_, 0, v___x_1567_);
                lean_ctor_set(v___x_1569_, 1, v___x_1568_);
                v___x_1570_ = l_Lean_MessageData_ofSyntax(v_after_1561_);
                v___x_1571_ = l_Lean_indentD(v___x_1570_);
                v_msgData_1572_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_1572_, 0, v___x_1569_);
                lean_ctor_set(v_msgData_1572_, 1, v___x_1571_);
                v___x_1573_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(v_msgData_1572_, v_macroStack_1548_);
                v___x_1574_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1574_, 0, v___x_1573_);
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___boxed(
    mut v_msgData_1578_: *mut LeanObject,
    mut v_macroStack_1579_: *mut LeanObject,
    mut v___y_1580_: *mut LeanObject,
    mut v___y_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1582_: *mut LeanObject = core::ptr::null_mut();
    v_res_1582_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_1578_, v_macroStack_1579_, v___y_1580_);
    lean_dec(v___y_1580_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(
    mut v_msg_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1597_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1602_: u8 = 0;
    let mut v_a_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1606_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1587_ = l_Lean_Elab_Command_getRef___redArg(v___y_1584_);
                if lean_obj_tag(v___x_1587_) == 0 {
                    v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
                    lean_inc(v_a_1588_);
                    lean_dec_ref_known(v___x_1587_, 1);
                    v_macroStack_1589_ = lean_ctor_get(v___y_1584_, 4);
                    v___x_1590_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msg_1583_, v___y_1585_);
                    v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
                    lean_inc(v_a_1591_);
                    lean_dec_ref(v___x_1590_);
                    v___x_1592_ = l_Lean_Elab_getBetterRef(v_a_1588_, v_macroStack_1589_);
                    lean_dec(v_a_1588_);
                    lean_inc(v_macroStack_1589_);
                    v___x_1593_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_a_1591_, v_macroStack_1589_, v___y_1585_);
                    v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
                    v_isSharedCheck_1602_ = (!lean_is_exclusive(v___x_1593_)) as u8;
                    if v_isSharedCheck_1602_ == 0 {
                        v___x_1596_ = v___x_1593_;
                        v_isShared_1597_ = v_isSharedCheck_1602_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1594_);
                        lean_dec(v___x_1593_);
                        v___x_1596_ = lean_box(0);
                        v_isShared_1597_ = v_isSharedCheck_1602_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_1583_);
                    v_a_1603_ = lean_ctor_get(v___x_1587_, 0);
                    v_isSharedCheck_1610_ = (!lean_is_exclusive(v___x_1587_)) as u8;
                    if v_isSharedCheck_1610_ == 0 {
                        v___x_1605_ = v___x_1587_;
                        v_isShared_1606_ = v_isSharedCheck_1610_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1603_);
                        lean_dec(v___x_1587_);
                        v___x_1605_ = lean_box(0);
                        v_isShared_1606_ = v_isSharedCheck_1610_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1598_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1598_, 0, v___x_1592_);
                lean_ctor_set(v___x_1598_, 1, v_a_1594_);
                if v_isShared_1597_ == 0 {
                    lean_ctor_set_tag(v___x_1596_, 1);
                    lean_ctor_set(v___x_1596_, 0, v___x_1598_);
                    v___x_1600_ = v___x_1596_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
                    v___x_1600_ = v_reuseFailAlloc_1601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1600_;
            }
            3 => {
                if v_isShared_1606_ == 0 {
                    v___x_1608_ = v___x_1605_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
                    v___x_1608_ = v_reuseFailAlloc_1609_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg___boxed(
    mut v_msg_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1615_: *mut LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_1611_, v___y_1612_, v___y_1613_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(
    mut v_ref_1616_: *mut LeanObject,
    mut v_msg_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1632_: u8 = 0;
    let mut v_ref_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = l_Lean_Elab_Command_getRef___redArg(v___y_1618_);
                if lean_obj_tag(v___x_1621_) == 0 {
                    v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
                    lean_inc(v_a_1622_);
                    lean_dec_ref_known(v___x_1621_, 1);
                    v_fileName_1623_ = lean_ctor_get(v___y_1618_, 0);
                    v_fileMap_1624_ = lean_ctor_get(v___y_1618_, 1);
                    v_currRecDepth_1625_ = lean_ctor_get(v___y_1618_, 2);
                    v_cmdPos_1626_ = lean_ctor_get(v___y_1618_, 3);
                    v_macroStack_1627_ = lean_ctor_get(v___y_1618_, 4);
                    v_quotContext_x3f_1628_ = lean_ctor_get(v___y_1618_, 5);
                    v_currMacroScope_1629_ = lean_ctor_get(v___y_1618_, 6);
                    v_snap_x3f_1630_ = lean_ctor_get(v___y_1618_, 8);
                    v_cancelTk_x3f_1631_ = lean_ctor_get(v___y_1618_, 9);
                    v_suppressElabErrors_1632_ = lean_ctor_get_uint8(
                        v___y_1618_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_1633_ = l_Lean_replaceRef(v_ref_1616_, v_a_1622_);
                    lean_dec(v_a_1622_);
                    lean_inc(v_cancelTk_x3f_1631_);
                    lean_inc(v_snap_x3f_1630_);
                    lean_inc(v_currMacroScope_1629_);
                    lean_inc(v_quotContext_x3f_1628_);
                    lean_inc(v_macroStack_1627_);
                    lean_inc(v_cmdPos_1626_);
                    lean_inc(v_currRecDepth_1625_);
                    lean_inc_ref(v_fileMap_1624_);
                    lean_inc_ref(v_fileName_1623_);
                    v___x_1634_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_1634_, 0, v_fileName_1623_);
                    lean_ctor_set(v___x_1634_, 1, v_fileMap_1624_);
                    lean_ctor_set(v___x_1634_, 2, v_currRecDepth_1625_);
                    lean_ctor_set(v___x_1634_, 3, v_cmdPos_1626_);
                    lean_ctor_set(v___x_1634_, 4, v_macroStack_1627_);
                    lean_ctor_set(v___x_1634_, 5, v_quotContext_x3f_1628_);
                    lean_ctor_set(v___x_1634_, 6, v_currMacroScope_1629_);
                    lean_ctor_set(v___x_1634_, 7, v_ref_1633_);
                    lean_ctor_set(v___x_1634_, 8, v_snap_x3f_1630_);
                    lean_ctor_set(v___x_1634_, 9, v_cancelTk_x3f_1631_);
                    lean_ctor_set_uint8(
                        v___x_1634_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_1632_,
                    );
                    v___x_1635_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_1617_, v___x_1634_, v___y_1619_);
                    lean_dec_ref_known(v___x_1634_, 10);
                    return v___x_1635_;
                } else {
                    lean_dec_ref(v_msg_1617_);
                    v_a_1636_ = lean_ctor_get(v___x_1621_, 0);
                    v_isSharedCheck_1643_ = (!lean_is_exclusive(v___x_1621_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v___x_1638_ = v___x_1621_;
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1636_);
                        lean_dec(v___x_1621_);
                        v___x_1638_ = lean_box(0);
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg___boxed(
    mut v_ref_1644_: *mut LeanObject,
    mut v_msg_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_1644_, v_msg_1645_, v___y_1646_, v___y_1647_);
    lean_dec(v___y_1647_);
    lean_dec_ref(v___y_1646_);
    lean_dec(v_ref_1644_);
    return v_res_1649_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0;
    v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2;
    v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
    return v___x_1655_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4;
    v___x_1658_ = l_Lean_stringToMessageData(v___x_1657_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6;
    v___x_1661_ = l_Lean_stringToMessageData(v___x_1660_);
    return v___x_1661_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8;
    v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
    return v___x_1664_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10;
    v___x_1667_ = l_Lean_stringToMessageData(v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12;
    v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(
    mut v_msg_1671_: *mut LeanObject,
    mut v_declHint_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: u8 = 0;
    let mut v_isExporting_1678_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1675_ = lean_st_ref_get(v___y_1673_);
                v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
                lean_inc_ref(v_env_1676_);
                lean_dec(v___x_1675_);
                v___x_1677_ = l_Lean_Name_isAnonymous(v_declHint_1672_);
                if v___x_1677_ == 0 {
                    v_isExporting_1678_ = lean_ctor_get_uint8(
                        v_env_1676_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1678_ == 0 {
                        lean_dec_ref(v_env_1676_);
                        lean_dec(v_declHint_1672_);
                        v___x_1679_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1679_, 0, v_msg_1671_);
                        return v___x_1679_;
                    } else {
                        lean_inc_ref(v_env_1676_);
                        v___x_1680_ = l_Lean_Environment_setExporting(v_env_1676_, v___x_1677_);
                        lean_inc(v_declHint_1672_);
                        lean_inc_ref(v___x_1680_);
                        v___x_1681_ = l_Lean_Environment_contains(
                            v___x_1680_,
                            v_declHint_1672_,
                            v_isExporting_1678_,
                        );
                        if v___x_1681_ == 0 {
                            lean_dec_ref(v___x_1680_);
                            lean_dec_ref(v_env_1676_);
                            lean_dec(v_declHint_1672_);
                            v___x_1682_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1682_, 0, v_msg_1671_);
                            return v___x_1682_;
                        } else {
                            v___x_1683_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
                            v___x_1684_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
                            v___x_1685_ = l_Lean_Options_empty;
                            v___x_1686_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1686_, 0, v___x_1680_);
                            lean_ctor_set(v___x_1686_, 1, v___x_1683_);
                            lean_ctor_set(v___x_1686_, 2, v___x_1684_);
                            lean_ctor_set(v___x_1686_, 3, v___x_1685_);
                            lean_inc(v_declHint_1672_);
                            v___x_1687_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1672_, v___x_1677_);
                            v_c_1688_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1688_, 0, v___x_1686_);
                            lean_ctor_set(v_c_1688_, 1, v___x_1687_);
                            v___x_1689_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1676_,
                                v_declHint_1672_,
                            );
                            if lean_obj_tag(v___x_1689_) == 0 {
                                lean_dec_ref(v_env_1676_);
                                lean_dec(v_declHint_1672_);
                                v___x_1690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
                                v___x_1691_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1691_, 0, v___x_1690_);
                                lean_ctor_set(v___x_1691_, 1, v_c_1688_);
                                v___x_1692_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3);
                                v___x_1693_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1693_, 0, v___x_1691_);
                                lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                                v___x_1694_ = l_Lean_MessageData_note(v___x_1693_);
                                v___x_1695_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1695_, 0, v_msg_1671_);
                                lean_ctor_set(v___x_1695_, 1, v___x_1694_);
                                v___x_1696_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1696_, 0, v___x_1695_);
                                return v___x_1696_;
                            } else {
                                v_val_1697_ = lean_ctor_get(v___x_1689_, 0);
                                v_isSharedCheck_1732_ = (!lean_is_exclusive(v___x_1689_)) as u8;
                                if v_isSharedCheck_1732_ == 0 {
                                    v___x_1699_ = v___x_1689_;
                                    v_isShared_1700_ = v_isSharedCheck_1732_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1697_);
                                    lean_dec(v___x_1689_);
                                    v___x_1699_ = lean_box(0);
                                    v_isShared_1700_ = v_isSharedCheck_1732_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1676_);
                    lean_dec(v_declHint_1672_);
                    v___x_1733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1733_, 0, v_msg_1671_);
                    return v___x_1733_;
                }
            }
            1 => {
                v___x_1701_ = lean_box(0);
                v___x_1702_ = l_Lean_Environment_header(v_env_1676_);
                lean_dec_ref(v_env_1676_);
                v___x_1703_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1702_);
                v_mod_1704_ = lean_array_get(v___x_1701_, v___x_1703_, v_val_1697_);
                lean_dec(v_val_1697_);
                lean_dec_ref(v___x_1703_);
                v___x_1705_ = l_Lean_isPrivateName(v_declHint_1672_);
                lean_dec(v_declHint_1672_);
                if v___x_1705_ == 0 {
                    v___x_1706_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5);
                    v___x_1707_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1707_, 0, v___x_1706_);
                    lean_ctor_set(v___x_1707_, 1, v_c_1688_);
                    v___x_1708_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7);
                    v___x_1709_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1709_, 0, v___x_1707_);
                    lean_ctor_set(v___x_1709_, 1, v___x_1708_);
                    v___x_1710_ = l_Lean_MessageData_ofName(v_mod_1704_);
                    v___x_1711_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1711_, 0, v___x_1709_);
                    lean_ctor_set(v___x_1711_, 1, v___x_1710_);
                    v___x_1712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9);
                    v___x_1713_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1713_, 0, v___x_1711_);
                    lean_ctor_set(v___x_1713_, 1, v___x_1712_);
                    v___x_1714_ = l_Lean_MessageData_note(v___x_1713_);
                    v___x_1715_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1715_, 0, v_msg_1671_);
                    lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                    if v_isShared_1700_ == 0 {
                        lean_ctor_set_tag(v___x_1699_, 0);
                        lean_ctor_set(v___x_1699_, 0, v___x_1715_);
                        v___x_1717_ = v___x_1699_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
                        v___x_1717_ = v_reuseFailAlloc_1718_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
                    v___x_1720_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1720_, 0, v___x_1719_);
                    lean_ctor_set(v___x_1720_, 1, v_c_1688_);
                    v___x_1721_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11);
                    v___x_1722_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1722_, 0, v___x_1720_);
                    lean_ctor_set(v___x_1722_, 1, v___x_1721_);
                    v___x_1723_ = l_Lean_MessageData_ofName(v_mod_1704_);
                    v___x_1724_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1724_, 0, v___x_1722_);
                    lean_ctor_set(v___x_1724_, 1, v___x_1723_);
                    v___x_1725_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13);
                    v___x_1726_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1726_, 0, v___x_1724_);
                    lean_ctor_set(v___x_1726_, 1, v___x_1725_);
                    v___x_1727_ = l_Lean_MessageData_note(v___x_1726_);
                    v___x_1728_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1728_, 0, v_msg_1671_);
                    lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                    if v_isShared_1700_ == 0 {
                        lean_ctor_set_tag(v___x_1699_, 0);
                        lean_ctor_set(v___x_1699_, 0, v___x_1728_);
                        v___x_1730_ = v___x_1699_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                        v___x_1730_ = v_reuseFailAlloc_1731_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1717_;
            }
            3 => {
                return v___x_1730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___boxed(
    mut v_msg_1734_: *mut LeanObject,
    mut v_declHint_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
    mut v___y_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1738_: *mut LeanObject = core::ptr::null_mut();
    v_res_1738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_1734_, v_declHint_1735_, v___y_1736_);
    lean_dec(v___y_1736_);
    return v_res_1738_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(
    mut v_msg_1739_: *mut LeanObject,
    mut v_declHint_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_1739_, v_declHint_1740_, v___y_1742_);
                v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
                v_isSharedCheck_1754_ = (!lean_is_exclusive(v___x_1744_)) as u8;
                if v_isSharedCheck_1754_ == 0 {
                    v___x_1747_ = v___x_1744_;
                    v_isShared_1748_ = v_isSharedCheck_1754_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1745_);
                    lean_dec(v___x_1744_);
                    v___x_1747_ = lean_box(0);
                    v_isShared_1748_ = v_isSharedCheck_1754_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1749_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1750_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1750_, 0, v___x_1749_);
                lean_ctor_set(v___x_1750_, 1, v_a_1745_);
                if v_isShared_1748_ == 0 {
                    lean_ctor_set(v___x_1747_, 0, v___x_1750_);
                    v___x_1752_ = v___x_1747_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10___boxed(
    mut v_msg_1755_: *mut LeanObject,
    mut v_declHint_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1760_: *mut LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_1755_, v_declHint_1756_, v___y_1757_, v___y_1758_);
    lean_dec(v___y_1758_);
    lean_dec_ref(v___y_1757_);
    return v_res_1760_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(
    mut v_ref_1761_: *mut LeanObject,
    mut v_msg_1762_: *mut LeanObject,
    mut v_declHint_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1767_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_1762_, v_declHint_1763_, v___y_1764_, v___y_1765_);
    v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
    lean_inc(v_a_1768_);
    lean_dec_ref(v___x_1767_);
    v___x_1769_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_1761_, v_a_1768_, v___y_1764_, v___y_1765_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_ref_1770_: *mut LeanObject,
    mut v_msg_1771_: *mut LeanObject,
    mut v_declHint_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1776_: *mut LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_1770_, v_msg_1771_, v_declHint_1772_, v___y_1773_, v___y_1774_);
    lean_dec(v___y_1774_);
    lean_dec_ref(v___y_1773_);
    lean_dec(v_ref_1770_);
    return v_res_1776_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0;
    v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70;
    v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(
    mut v_ref_1782_: *mut LeanObject,
    mut v_constName_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    v___x_1787_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1);
    v___x_1788_ = 0;
    lean_inc(v_constName_1783_);
    v___x_1789_ = l_Lean_MessageData_ofConstName(v_constName_1783_, v___x_1788_);
    v___x_1790_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1790_, 0, v___x_1787_);
    lean_ctor_set(v___x_1790_, 1, v___x_1789_);
    v___x_1791_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2);
    v___x_1792_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1792_, 0, v___x_1790_);
    lean_ctor_set(v___x_1792_, 1, v___x_1791_);
    v___x_1793_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_1782_, v___x_1792_, v_constName_1783_, v___y_1784_, v___y_1785_);
    return v___x_1793_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___boxed(
    mut v_ref_1794_: *mut LeanObject,
    mut v_constName_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1799_: *mut LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_1794_, v_constName_1795_, v___y_1796_, v___y_1797_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    lean_dec(v_ref_1794_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(
    mut v_constName_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1804_ = l_Lean_Elab_Command_getRef___redArg(v___y_1801_);
                if lean_obj_tag(v___x_1804_) == 0 {
                    v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
                    lean_inc(v_a_1805_);
                    lean_dec_ref_known(v___x_1804_, 1);
                    v___x_1806_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_a_1805_, v_constName_1800_, v___y_1801_, v___y_1802_);
                    lean_dec(v_a_1805_);
                    return v___x_1806_;
                } else {
                    lean_dec(v_constName_1800_);
                    v_a_1807_ = lean_ctor_get(v___x_1804_, 0);
                    v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1804_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1804_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1807_);
                        lean_dec(v___x_1804_);
                        v___x_1809_ = lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg___boxed(
    mut v_constName_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1819_: *mut LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_1815_, v___y_1816_, v___y_1817_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    return v_res_1819_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(
    mut v_constName_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = lean_st_ref_get(v___y_1822_);
                v_env_1825_ = lean_ctor_get(v___x_1824_, 0);
                lean_inc_ref(v_env_1825_);
                lean_dec(v___x_1824_);
                v___x_1826_ = 0;
                lean_inc(v_constName_1820_);
                v___x_1827_ =
                    l_Lean_Environment_find_x3f(v_env_1825_, v_constName_1820_, v___x_1826_);
                if lean_obj_tag(v___x_1827_) == 0 {
                    v___x_1828_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_1820_, v___y_1821_, v___y_1822_);
                    return v___x_1828_;
                } else {
                    lean_dec(v_constName_1820_);
                    v_val_1829_ = lean_ctor_get(v___x_1827_, 0);
                    v_isSharedCheck_1836_ = (!lean_is_exclusive(v___x_1827_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v___x_1831_ = v___x_1827_;
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1829_);
                        lean_dec(v___x_1827_);
                        v___x_1831_ = lean_box(0);
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1832_ == 0 {
                    lean_ctor_set_tag(v___x_1831_, 0);
                    v___x_1834_ = v___x_1831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_val_1829_);
                    v___x_1834_ = v_reuseFailAlloc_1835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2___boxed(
    mut v_constName_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1841_: *mut LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_constName_1837_, v___y_1838_, v___y_1839_);
    lean_dec(v___y_1839_);
    lean_dec_ref(v___y_1838_);
    return v_res_1841_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1;
    v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(
    mut v_as_1846_: *mut LeanObject,
    mut v_sz_1847_: usize,
    mut v_i_1848_: usize,
    mut v_b_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: usize = 0;
    let mut v___x_1867_: usize = 0;
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1853_ = lean_usize_dec_lt(v_i_1848_, v_sz_1847_);
                if v___x_1853_ == 0 {
                    v___x_1854_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1854_, 0, v_b_1849_);
                    return v___x_1854_;
                } else {
                    v_a_1855_ = lean_array_uget_borrowed(v_as_1846_, v_i_1848_);
                    lean_inc(v_a_1855_);
                    v___x_1856_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_a_1855_, v___y_1850_, v___y_1851_);
                    if lean_obj_tag(v___x_1856_) == 0 {
                        v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
                        lean_inc(v_a_1857_);
                        lean_dec_ref_known(v___x_1856_, 1);
                        v___f_1858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0;
                        v___x_1859_ = lean_box(0);
                        lean_inc(v_a_1855_);
                        v___f_1860_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                        lean_closure_set(v___f_1860_, 0, v_a_1855_);
                        v___f_1861_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed as *mut core::ffi::c_void, 4, 1);
                        lean_closure_set(v___f_1861_, 0, v___f_1860_);
                        v___x_1869_ = l_Lean_ConstantInfo_levelParams(v_a_1857_);
                        lean_dec(v_a_1857_);
                        v___x_1870_ = l_List_isEmpty___redArg(v___x_1869_);
                        lean_dec(v___x_1869_);
                        if v___x_1870_ == 0 {
                            lean_inc(v_a_1855_);
                            v___x_1871_ = l_Lean_MessageData_ofConstName(v_a_1855_, v___x_1870_);
                            v___x_1872_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2);
                            v___x_1873_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1873_, 0, v___x_1871_);
                            lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                            v___x_1874_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v___x_1873_, v___y_1850_, v___y_1851_);
                            if lean_obj_tag(v___x_1874_) == 0 {
                                lean_dec_ref_known(v___x_1874_, 1);
                                v___y_1863_ = v___y_1850_;
                                v___y_1864_ = v___y_1851_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___f_1861_);
                                return v___x_1874_;
                            }
                        } else {
                            v___y_1863_ = v___y_1850_;
                            v___y_1864_ = v___y_1851_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
                        v_isSharedCheck_1882_ = (!lean_is_exclusive(v___x_1856_)) as u8;
                        if v_isSharedCheck_1882_ == 0 {
                            v___x_1877_ = v___x_1856_;
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1875_);
                            lean_dec(v___x_1856_);
                            v___x_1877_ = lean_box(0);
                            v_isShared_1878_ = v_isSharedCheck_1882_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1865_ = l_Lean_Elab_Command_withScope___redArg(
                    v___f_1858_,
                    v___f_1861_,
                    v___y_1863_,
                    v___y_1864_,
                );
                if lean_obj_tag(v___x_1865_) == 0 {
                    lean_dec_ref_known(v___x_1865_, 1);
                    v___x_1866_ = 1usize;
                    v___x_1867_ = lean_usize_add(v_i_1848_, v___x_1866_);
                    v_i_1848_ = v___x_1867_;
                    v_b_1849_ = v___x_1859_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1865_;
                }
            }
            2 => {
                if v_isShared_1878_ == 0 {
                    v___x_1880_ = v___x_1877_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
                    v___x_1880_ = v_reuseFailAlloc_1881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___boxed(
    mut v_as_1883_: *mut LeanObject,
    mut v_sz_1884_: *mut LeanObject,
    mut v_i_1885_: *mut LeanObject,
    mut v_b_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1890_: usize = 0;
    let mut v_i_boxed_1891_: usize = 0;
    let mut v_res_1892_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1890_ = lean_unbox_usize(v_sz_1884_);
    lean_dec(v_sz_1884_);
    v_i_boxed_1891_ = lean_unbox_usize(v_i_1885_);
    lean_dec(v_i_1885_);
    v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_as_1883_, v_sz_boxed_1890_, v_i_boxed_1891_, v_b_1886_, v___y_1887_, v___y_1888_);
    lean_dec(v___y_1888_);
    lean_dec_ref(v___y_1887_);
    lean_dec_ref(v_as_1883_);
    return v_res_1892_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(
    mut v_declNames_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1898_: usize = 0;
    let mut v___x_1899_: usize = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1903_: u8 = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_unused_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1897_ = lean_box(0);
                v_sz_1898_ = lean_array_size(v_declNames_1893_);
                v___x_1899_ = 0usize;
                v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_declNames_1893_, v_sz_1898_, v___x_1899_, v___x_1897_, v_a_1894_, v_a_1895_);
                if lean_obj_tag(v___x_1900_) == 0 {
                    v_isSharedCheck_1909_ = (!lean_is_exclusive(v___x_1900_)) as u8;
                    if v_isSharedCheck_1909_ == 0 {
                        v_unused_1910_ = lean_ctor_get(v___x_1900_, 0);
                        lean_dec(v_unused_1910_);
                        v___x_1902_ = v___x_1900_;
                        v_isShared_1903_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1900_);
                        v___x_1902_ = lean_box(0);
                        v_isShared_1903_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1911_ = lean_ctor_get(v___x_1900_, 0);
                    v_isSharedCheck_1918_ = (!lean_is_exclusive(v___x_1900_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1913_ = v___x_1900_;
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1911_);
                        lean_dec(v___x_1900_);
                        v___x_1913_ = lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1904_ = 1;
                v___x_1905_ = lean_box((v___x_1904_) as usize);
                if v_isShared_1903_ == 0 {
                    lean_ctor_set(v___x_1902_, 0, v___x_1905_);
                    v___x_1907_ = v___x_1902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
                    v___x_1907_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1907_;
            }
            3 => {
                if v_isShared_1914_ == 0 {
                    v___x_1916_ = v___x_1913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(
    mut v_declNames_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(
        v_declNames_1919_,
        v_a_1920_,
        v_a_1921_,
    );
    lean_dec(v_a_1921_);
    lean_dec_ref(v_a_1920_);
    lean_dec_ref(v_declNames_1919_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(
    mut v_msgData_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_1924_, v___y_1926_);
    return v___x_1928_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___boxed(
    mut v_msgData_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(v_msgData_1929_, v___y_1930_, v___y_1931_);
    lean_dec(v___y_1931_);
    lean_dec_ref(v___y_1930_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(
    mut v_00_u03b1_1934_: *mut LeanObject,
    mut v_msg_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    v___x_1939_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_1935_, v___y_1936_, v___y_1937_);
    return v___x_1939_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___boxed(
    mut v_00_u03b1_1940_: *mut LeanObject,
    mut v_msg_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(v_00_u03b1_1940_, v_msg_1941_, v___y_1942_, v___y_1943_);
    lean_dec(v___y_1943_);
    lean_dec_ref(v___y_1942_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(
    mut v_00_u03b1_1946_: *mut LeanObject,
    mut v_constName_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    v___x_1951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_1947_, v___y_1948_, v___y_1949_);
    return v___x_1951_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___boxed(
    mut v_00_u03b1_1952_: *mut LeanObject,
    mut v_constName_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1957_: *mut LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(v_00_u03b1_1952_, v_constName_1953_, v___y_1954_, v___y_1955_);
    lean_dec(v___y_1955_);
    lean_dec_ref(v___y_1954_);
    return v_res_1957_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(
    mut v_msgData_1958_: *mut LeanObject,
    mut v_macroStack_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_1958_, v_macroStack_1959_, v___y_1961_);
    return v___x_1963_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___boxed(
    mut v_msgData_1964_: *mut LeanObject,
    mut v_macroStack_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1969_: *mut LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(v_msgData_1964_, v_macroStack_1965_, v___y_1966_, v___y_1967_);
    lean_dec(v___y_1967_);
    lean_dec_ref(v___y_1966_);
    return v_res_1969_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(
    mut v_00_u03b1_1970_: *mut LeanObject,
    mut v_ref_1971_: *mut LeanObject,
    mut v_constName_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_1971_, v_constName_1972_, v___y_1973_, v___y_1974_);
    return v___x_1976_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___boxed(
    mut v_00_u03b1_1977_: *mut LeanObject,
    mut v_ref_1978_: *mut LeanObject,
    mut v_constName_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1983_: *mut LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(v_00_u03b1_1977_, v_ref_1978_, v_constName_1979_, v___y_1980_, v___y_1981_);
    lean_dec(v___y_1981_);
    lean_dec_ref(v___y_1980_);
    lean_dec(v_ref_1978_);
    return v_res_1983_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(
    mut v_00_u03b1_1984_: *mut LeanObject,
    mut v_ref_1985_: *mut LeanObject,
    mut v_msg_1986_: *mut LeanObject,
    mut v_declHint_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_1985_, v_msg_1986_, v_declHint_1987_, v___y_1988_, v___y_1989_);
    return v___x_1991_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___boxed(
    mut v_00_u03b1_1992_: *mut LeanObject,
    mut v_ref_1993_: *mut LeanObject,
    mut v_msg_1994_: *mut LeanObject,
    mut v_declHint_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1999_: *mut LeanObject = core::ptr::null_mut();
    v_res_1999_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(v_00_u03b1_1992_, v_ref_1993_, v_msg_1994_, v_declHint_1995_, v___y_1996_, v___y_1997_);
    lean_dec(v___y_1997_);
    lean_dec_ref(v___y_1996_);
    lean_dec(v_ref_1993_);
    return v_res_1999_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(
    mut v_msg_2000_: *mut LeanObject,
    mut v_declHint_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v___x_2005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_2000_, v_declHint_2001_, v___y_2003_);
    return v___x_2005_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___boxed(
    mut v_msg_2006_: *mut LeanObject,
    mut v_declHint_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2011_: *mut LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(v_msg_2006_, v_declHint_2007_, v___y_2008_, v___y_2009_);
    lean_dec(v___y_2009_);
    lean_dec_ref(v___y_2008_);
    return v_res_2011_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(
    mut v_00_u03b1_2012_: *mut LeanObject,
    mut v_ref_2013_: *mut LeanObject,
    mut v_msg_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_2013_, v_msg_2014_, v___y_2015_, v___y_2016_);
    return v___x_2018_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___boxed(
    mut v_00_u03b1_2019_: *mut LeanObject,
    mut v_ref_2020_: *mut LeanObject,
    mut v_msg_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2025_: *mut LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(v_00_u03b1_2019_, v_ref_2020_, v_msg_2021_, v___y_2022_, v___y_2023_);
    lean_dec(v___y_2023_);
    lean_dec_ref(v___y_2022_);
    lean_dec(v_ref_2020_);
    return v_res_2025_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48;
    v___x_2029_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_;
    v___x_2030_ = l_Lean_Elab_registerDerivingHandler(v___x_2028_, v___x_2029_);
    return v___x_2030_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2____boxed(
    mut v_a_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2032_: *mut LeanObject = core::ptr::null_mut();
    v_res_2032_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
    return v_res_2032_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_TypeName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_TypeName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Deriving_TypeName(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_TypeName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_TypeName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_TypeName(builtin);
}
