// Lean compiler output
// Module: Lean.Elab.Import
// Imports: Lean.Parser.Module Lean.Parser.Module Lean.Compiler.ModPkgExt Lean.DeprecatedModule Init.Data.String.Modify
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_get_stdout,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq,
    lean_string_get_byte_fast, lean_string_push, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_string_utf8_set, lean_uint8_dec_eq, lean_uint32_add, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posGE___redArg;
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getTrailing_x3f, l_Lean_Syntax_isNone, l_Lean_TSyntax_getId,
};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::ModPkgExt::{
    initialize_Lean_Compiler_ModPkgExt, l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt,
    runtime_initialize_Lean_Compiler_ModPkgExt,
};
use crate::r#gen::Lean::CoreM::l_Lean_Elab_inServer;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeprecatedModule::{
    initialize_Lean_DeprecatedModule, l_Lean_Environment_getDeprecatedModuleByIdx_x3f,
    l_Lean_formatDeprecatedModuleWarning, l_Lean_linter_deprecated_module,
    runtime_initialize_Lean_DeprecatedModule,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdx_x3f, l_Lean_Environment_setMainModule,
    l_Lean_PersistentEnvExtension_setState___redArg, l_Lean_importModules,
    lean_mk_empty_environment,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add};
use crate::r#gen::Lean::Parser::Extension::l_Lean_Parser_mkInputContext___redArg;
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, l_Lean_Parser_parseHeader, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::Setup::l_Lean_instInhabitedImport_default;
use crate::r#gen::Lean::Util::Path::{l_Lean_findLean, l_Lean_findOLean, l_Lean_getSrcSearchPath};
static mut l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 109, 112, 111, 114, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__3_value) as *mut leanh::LeanObject,3187861556840815537 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 73, 109, 112, 111, 114, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 72, 101, 97, 100, 101, 114, 83, 121, 110, 116, 97, 120, 46, 105, 109, 112, 111, 114, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__9_value) as *mut leanh::LeanObject,9485984681193916779 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__11_value) as *mut leanh::LeanObject,17003524124175295577 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__13_value) as *mut leanh::LeanObject,12460543829726897862 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_HeaderSyntax_imports___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [104, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_HeaderSyntax_imports___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__0_value)
                as *mut leanh::LeanObject,
            14592748414440353064 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_HeaderSyntax_imports___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_HeaderSyntax_imports___closed__3_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_HeaderSyntax_imports___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_HeaderSyntax_imports___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [73, 110, 105, 116, 0],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_HeaderSyntax_imports___closed__5_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__4_value)
                as *mut leanh::LeanObject,
            1882184448842950296 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_HeaderSyntax_imports___closed__6_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 114, 101, 108, 117, 100, 101, 0],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_HeaderSyntax_imports___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__6_value)
                as *mut leanh::LeanObject,
            17898809269769340598 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_HeaderSyntax_imports___closed__8_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [109, 111, 100, 117, 108, 101, 84, 107, 0],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_HeaderSyntax_imports___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__9_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__8_value)
                as *mut leanh::LeanObject,
            15944969286361870278 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_HeaderSyntax_imports___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_HeaderSyntax_imports___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 95, 109, 111, 100, 117, 108, 101, 58, 32, 105, 103, 110, 111, 114, 101, 0]};
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0_value
) as *mut leanh::LeanObject;
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2:
    u8 = 0;
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 77, 111, 100, 117, 108, 101, 69, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__1_value) as *mut leanh::LeanObject,14236438790327215984 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [67, 79, 78, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [80, 82, 78, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 85, 88, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 85, 76, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 49, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 50, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 51, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 52, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 53, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 54, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 55, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 56, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 79, 77, 57, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [67, 79, 77, 194, 185, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [67, 79, 77, 194, 178, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [67, 79, 77, 194, 179, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 49, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 50, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 51, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 52, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 53, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 54, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 55, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 56, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 80, 84, 57, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [76, 80, 84, 194, 185, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [76, 80, 84, 194, 178, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 4,
    m_data: [76, 80, 84, 194, 179, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value:
    leanh::LeanArrayObject<28> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 28) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 28,
    m_capacity: 28,
    m_data: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__5_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__6_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__7_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__9_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__10_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__11_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__12_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__13_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__14_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__15_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__16_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__17_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__18_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__19_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__20_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__21_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__22_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__23_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__24_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__25_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__26_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__27_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames___closed__28_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0: usize =
    0;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
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
        99, 111, 110, 116, 97, 105, 110, 115, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 32, 39,
        0,
    ],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2_value:
    leanh::LeanStringObject<47> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        39, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 102, 111, 114, 98, 105, 100, 100, 101,
        110, 32, 111, 110, 32, 115, 111, 109, 101, 32, 111, 112, 101, 114, 97, 116, 105, 110, 103,
        32, 115, 121, 115, 116, 101, 109, 115, 0,
    ],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4_value:
    leanh::LeanStringObject<52> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        39, 32, 105, 115, 32, 97, 32, 114, 101, 115, 101, 114, 118, 101, 100, 32, 102, 105, 108,
        101, 32, 110, 97, 109, 101, 32, 111, 110, 32, 115, 111, 109, 101, 32, 111, 112, 101, 114,
        97, 116, 105, 110, 103, 32, 115, 121, 115, 116, 101, 109, 115, 0,
    ],
};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 111, 100, 117, 108, 101, 32, 110, 97, 109, 101, 32, 39, 0]};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [39, 32, 105, 115, 32, 110, 111, 116, 32, 112, 111, 114, 116, 97, 98, 108, 101, 58, 32, 0]};
static mut l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_parseImports___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [60, 105, 110, 112, 117, 116, 62, 0],
    };
static mut l_Lean_Elab_parseImports___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_parseImports___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_HeaderSyntax_startPos(
    mut v_header_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = 0;
    v___x_1342_ = l_Lean_Syntax_getPos_x3f(v_header_1340_, v___x_1341_);
    if leanh::lean_obj_tag(v___x_1342_) == 0 {
        let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1343_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1343_;
    } else {
        let mut v_val_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1344_ = leanh::lean_ctor_get(v___x_1342_, 0);
        leanh::lean_inc(v_val_1344_);
        leanh::lean_dec_ref_known(v___x_1342_, 1);
        return v_val_1344_;
    }
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_startPos___boxed(
    mut v_header_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_1345_);
    leanh::lean_dec(v_header_1345_);
    return v_res_1346_;
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_isModule(
    mut v_header_1347_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    v___x_1348_ = leanh::lean_unsigned_to_nat(0);
    v___x_1349_ = l_Lean_Syntax_getArg(v_header_1347_, v___x_1348_);
    v___x_1350_ = l_Lean_Syntax_isNone(v___x_1349_);
    leanh::lean_dec(v___x_1349_);
    if v___x_1350_ == 0 {
        let mut v___x_1351_: u8 = 0;
        v___x_1351_ = 1;
        return v___x_1351_;
    } else {
        let mut v___x_1352_: u8 = 0;
        v___x_1352_ = 0;
        return v___x_1352_;
    }
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_isModule___boxed(
    mut v_header_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: u8 = 0;
    let mut v_r_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_1353_);
    leanh::lean_dec(v_header_1353_);
    v_r_1355_ = leanh::lean_box((v_res_1354_) as usize);
    return v_r_1355_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1356_;
}
pub unsafe fn l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(
    mut v_msg_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0___closed__0,
    );
    v___x_1359_ = lean_panic_fn_borrowed(v___x_1358_, v_msg_1357_);
    return v___x_1359_;
}
pub unsafe fn l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(
    mut v_msg_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = l_Lean_instInhabitedImport_default;
    v___x_1362_ = lean_panic_fn_borrowed(v___x_1361_, v_msg_1360_);
    return v___x_1362_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7;
    v___x_1376_ = leanh::lean_unsigned_to_nat(13);
    v___x_1377_ = leanh::lean_unsigned_to_nat(40);
    v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6;
    v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5;
    v___x_1380_ = l_mkPanicMessageWithDecl(
        v___x_1379_,
        v___x_1378_,
        v___x_1377_,
        v___x_1376_,
        v___x_1375_,
    );
    return v___x_1380_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(
    mut v_moduleTk_1399_: *mut leanh::LeanObject,
    mut v___x_1400_: u8,
    mut v_sz_1401_: usize,
    mut v_i_1402_: usize,
    mut v_bs_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: usize = 0;
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: u8 = 0;
    let mut v___y_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: u8 = 0;
    let mut v___y_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: u8 = 0;
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: u8 = 0;
    let mut v___y_1427_: u8 = 0;
    let mut v___y_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1429_: u8 = 0;
    let mut v___y_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1433_: u8 = 0;
    let mut v___y_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1435_: u8 = 0;
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allTk_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaTk_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allTk_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_publicTk_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaTk_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_publicTk_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1404_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
                if v___x_1404_ == 0 {
                    return v_bs_1403_;
                } else {
                    v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4;
                    v_v_1406_ = lean_array_uget(v_bs_1403_, v_i_1402_);
                    v___x_1407_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1408_ = lean_array_uset(v_bs_1403_, v_i_1402_, v___x_1407_);
                    leanh::lean_inc(v_v_1406_);
                    v___x_1437_ = l_Lean_Syntax_isOfKind(v_v_1406_, v___x_1405_);
                    if v___x_1437_ == 0 {
                        leanh::lean_dec(v_v_1406_);
                        v___x_1438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                        v___x_1439_ =
                            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_1438_);
                        v___y_1410_ = v___x_1439_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1453_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1486_ = l_Lean_Syntax_getArg(v_v_1406_, v___x_1407_);
                        v___x_1487_ = l_Lean_Syntax_isNone(v___x_1486_);
                        if v___x_1487_ == 0 {
                            leanh::lean_inc(v___x_1486_);
                            v___x_1488_ = l_Lean_Syntax_matchesNull(v___x_1486_, v___x_1453_);
                            if v___x_1488_ == 0 {
                                leanh::lean_dec(v___x_1486_);
                                leanh::lean_dec(v_v_1406_);
                                v___x_1489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                                v___x_1490_ =
                                    l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(
                                        v___x_1489_,
                                    );
                                v___y_1410_ = v___x_1490_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1491_ = l_Lean_Syntax_getArg(v___x_1486_, v___x_1407_);
                                leanh::lean_dec(v___x_1486_);
                                v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14;
                                leanh::lean_inc(v___x_1491_);
                                v___x_1493_ = l_Lean_Syntax_isOfKind(v___x_1491_, v___x_1492_);
                                if v___x_1493_ == 0 {
                                    leanh::lean_dec(v___x_1491_);
                                    leanh::lean_dec(v_v_1406_);
                                    v___x_1494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                                    v___x_1495_ =
                                        l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(
                                            v___x_1494_,
                                        );
                                    v___y_1410_ = v___x_1495_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_publicTk_1496_ =
                                        l_Lean_Syntax_getArg(v___x_1491_, v___x_1407_);
                                    leanh::lean_dec(v___x_1491_);
                                    v___x_1497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1497_, 0, v_publicTk_1496_);
                                    v_publicTk_1472_ = v___x_1497_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1486_);
                            v___x_1498_ = leanh::lean_box(0);
                            v_publicTk_1472_ = v___x_1498_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1411_ = 1usize;
                v___x_1412_ = lean_usize_add(v_i_1402_, v___x_1411_);
                v___x_1413_ = lean_array_uset(v_bs_x27_1408_, v_i_1402_, v___y_1410_);
                v_i_1402_ = v___x_1412_;
                v_bs_1403_ = v___x_1413_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_1419_) == 0 {
                    v___x_1421_ = 0;
                    v___x_1422_ = leanh::lean_alloc_ctor(0, 1, (3) as u32);
                    leanh::lean_ctor_set(v___x_1422_, 0, v___y_1417_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1422_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___y_1416_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1422_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                        v___y_1420_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1422_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                        v___x_1421_,
                    );
                    v___y_1410_ = v___x_1422_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___y_1419_, 1);
                    v___x_1423_ = leanh::lean_alloc_ctor(0, 1, (3) as u32);
                    leanh::lean_ctor_set(v___x_1423_, 0, v___y_1417_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1423_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___y_1416_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1423_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                        v___y_1420_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1423_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                        v___y_1418_,
                    );
                    v___y_1410_ = v___x_1423_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_moduleTk_1399_) == 0 {
                    v___y_1416_ = v___y_1426_;
                    v___y_1417_ = v___y_1425_;
                    v___y_1418_ = v___y_1427_;
                    v___y_1419_ = v___y_1428_;
                    v___y_1420_ = v___y_1427_;
                    state = 2;
                    continue;
                } else {
                    v___y_1416_ = v___y_1426_;
                    v___y_1417_ = v___y_1425_;
                    v___y_1418_ = v___y_1427_;
                    v___y_1419_ = v___y_1428_;
                    v___y_1420_ = v___y_1429_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if leanh::lean_obj_tag(v___y_1431_) == 0 {
                    v___x_1436_ = 0;
                    v___y_1425_ = v___y_1432_;
                    v___y_1426_ = v___y_1435_;
                    v___y_1427_ = v___y_1433_;
                    v___y_1428_ = v___y_1434_;
                    v___y_1429_ = v___x_1436_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___y_1431_, 1);
                    if v___y_1433_ == 0 {
                        v___y_1425_ = v___y_1432_;
                        v___y_1426_ = v___y_1435_;
                        v___y_1427_ = v___y_1433_;
                        v___y_1428_ = v___y_1434_;
                        v___y_1429_ = v___y_1433_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1416_ = v___y_1435_;
                        v___y_1417_ = v___y_1432_;
                        v___y_1418_ = v___y_1433_;
                        v___y_1419_ = v___y_1434_;
                        v___y_1420_ = v___x_1400_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1444_ = leanh::lean_unsigned_to_nat(5);
                v___x_1445_ = l_Lean_Syntax_getArg(v_v_1406_, v___x_1444_);
                v___x_1446_ = l_Lean_Syntax_matchesNull(v___x_1445_, v___x_1407_);
                if v___x_1446_ == 0 {
                    leanh::lean_dec(v_allTk_1443_);
                    leanh::lean_dec(v___y_1442_);
                    leanh::lean_dec(v___y_1441_);
                    leanh::lean_dec(v_v_1406_);
                    v___x_1447_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                    v___x_1448_ =
                        l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_1447_);
                    v___y_1410_ = v___x_1448_;
                    state = 1;
                    continue;
                } else {
                    v___x_1449_ = leanh::lean_unsigned_to_nat(4);
                    v_n_1450_ = l_Lean_Syntax_getArg(v_v_1406_, v___x_1449_);
                    leanh::lean_dec(v_v_1406_);
                    v___x_1451_ = l_Lean_TSyntax_getId(v_n_1450_);
                    leanh::lean_dec(v_n_1450_);
                    if leanh::lean_obj_tag(v_allTk_1443_) == 0 {
                        v___x_1452_ = 0;
                        v___y_1431_ = v___y_1441_;
                        v___y_1432_ = v___x_1451_;
                        v___y_1433_ = v___x_1446_;
                        v___y_1434_ = v___y_1442_;
                        v___y_1435_ = v___x_1452_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_allTk_1443_, 1);
                        v___y_1431_ = v___y_1441_;
                        v___y_1432_ = v___x_1451_;
                        v___y_1433_ = v___x_1446_;
                        v___y_1434_ = v___y_1442_;
                        v___y_1435_ = v___x_1446_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1457_ = leanh::lean_unsigned_to_nat(3);
                v___x_1458_ = l_Lean_Syntax_getArg(v_v_1406_, v___x_1457_);
                v___x_1459_ = l_Lean_Syntax_isNone(v___x_1458_);
                if v___x_1459_ == 0 {
                    leanh::lean_inc(v___x_1458_);
                    v___x_1460_ = l_Lean_Syntax_matchesNull(v___x_1458_, v___x_1453_);
                    if v___x_1460_ == 0 {
                        leanh::lean_dec(v___x_1458_);
                        leanh::lean_dec(v_metaTk_1456_);
                        leanh::lean_dec(v___y_1455_);
                        leanh::lean_dec(v_v_1406_);
                        v___x_1461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                        v___x_1462_ =
                            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_1461_);
                        v___y_1410_ = v___x_1462_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1463_ = l_Lean_Syntax_getArg(v___x_1458_, v___x_1407_);
                        leanh::lean_dec(v___x_1458_);
                        v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10;
                        leanh::lean_inc(v___x_1463_);
                        v___x_1465_ = l_Lean_Syntax_isOfKind(v___x_1463_, v___x_1464_);
                        if v___x_1465_ == 0 {
                            leanh::lean_dec(v___x_1463_);
                            leanh::lean_dec(v_metaTk_1456_);
                            leanh::lean_dec(v___y_1455_);
                            leanh::lean_dec(v_v_1406_);
                            v___x_1466_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                            v___x_1467_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(
                                v___x_1466_,
                            );
                            v___y_1410_ = v___x_1467_;
                            state = 1;
                            continue;
                        } else {
                            v_allTk_1468_ = l_Lean_Syntax_getArg(v___x_1463_, v___x_1407_);
                            leanh::lean_dec(v___x_1463_);
                            v___x_1469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1469_, 0, v_allTk_1468_);
                            v___y_1441_ = v___y_1455_;
                            v___y_1442_ = v_metaTk_1456_;
                            v_allTk_1443_ = v___x_1469_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1458_);
                    v___x_1470_ = leanh::lean_box(0);
                    v___y_1441_ = v___y_1455_;
                    v___y_1442_ = v_metaTk_1456_;
                    v_allTk_1443_ = v___x_1470_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_1473_ = l_Lean_Syntax_getArg(v_v_1406_, v___x_1453_);
                v___x_1474_ = l_Lean_Syntax_isNone(v___x_1473_);
                if v___x_1474_ == 0 {
                    leanh::lean_inc(v___x_1473_);
                    v___x_1475_ = l_Lean_Syntax_matchesNull(v___x_1473_, v___x_1453_);
                    if v___x_1475_ == 0 {
                        leanh::lean_dec(v___x_1473_);
                        leanh::lean_dec(v_publicTk_1472_);
                        leanh::lean_dec(v_v_1406_);
                        v___x_1476_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                        v___x_1477_ =
                            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(v___x_1476_);
                        v___y_1410_ = v___x_1477_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1478_ = l_Lean_Syntax_getArg(v___x_1473_, v___x_1407_);
                        leanh::lean_dec(v___x_1473_);
                        v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12;
                        leanh::lean_inc(v___x_1478_);
                        v___x_1480_ = l_Lean_Syntax_isOfKind(v___x_1478_, v___x_1479_);
                        if v___x_1480_ == 0 {
                            leanh::lean_dec(v___x_1478_);
                            leanh::lean_dec(v_publicTk_1472_);
                            leanh::lean_dec(v_v_1406_);
                            v___x_1481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__8);
                            v___x_1482_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__1(
                                v___x_1481_,
                            );
                            v___y_1410_ = v___x_1482_;
                            state = 1;
                            continue;
                        } else {
                            v_metaTk_1483_ = l_Lean_Syntax_getArg(v___x_1478_, v___x_1407_);
                            leanh::lean_dec(v___x_1478_);
                            v___x_1484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1484_, 0, v_metaTk_1483_);
                            v___y_1455_ = v_publicTk_1472_;
                            v_metaTk_1456_ = v___x_1484_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1473_);
                    v___x_1485_ = leanh::lean_box(0);
                    v___y_1455_ = v_publicTk_1472_;
                    v_metaTk_1456_ = v___x_1485_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___boxed(
    mut v_moduleTk_1499_: *mut leanh::LeanObject,
    mut v___x_1500_: *mut leanh::LeanObject,
    mut v_sz_1501_: *mut leanh::LeanObject,
    mut v_i_1502_: *mut leanh::LeanObject,
    mut v_bs_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3706__boxed_1504_: u8 = 0;
    let mut v_sz_boxed_1505_: usize = 0;
    let mut v_i_boxed_1506_: usize = 0;
    let mut v_res_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3706__boxed_1504_ = (leanh::lean_unbox(v___x_1500_) as u8);
    v_sz_boxed_1505_ = leanh::lean_unbox_usize(v_sz_1501_);
    leanh::lean_dec(v_sz_1501_);
    v_i_boxed_1506_ = leanh::lean_unbox_usize(v_i_1502_);
    leanh::lean_dec(v_i_1502_);
    v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v_moduleTk_1499_, v___x_3706__boxed_1504_, v_sz_boxed_1505_, v_i_boxed_1506_, v_bs_1503_);
    leanh::lean_dec(v_moduleTk_1499_);
    return v_res_1507_;
}
pub unsafe fn _init_l_Lean_Elab_HeaderSyntax_imports___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__7;
    v___x_1515_ = leanh::lean_unsigned_to_nat(9);
    v___x_1516_ = leanh::lean_unsigned_to_nat(41);
    v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__6;
    v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__5;
    v___x_1519_ = l_mkPanicMessageWithDecl(
        v___x_1518_,
        v___x_1517_,
        v___x_1516_,
        v___x_1515_,
        v___x_1514_,
    );
    return v___x_1519_;
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_imports(
    mut v_stx_1537_: *mut leanh::LeanObject,
    mut v_includeInit_1538_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___y_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1545_: usize = 0;
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preludeTk_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importsStx_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleTk_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preludeTk_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleTk_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1539_ = l_Lean_Elab_HeaderSyntax_imports___closed__1;
                leanh::lean_inc(v_stx_1537_);
                v___x_1540_ = l_Lean_Syntax_isOfKind(v_stx_1537_, v___x_1539_);
                if v___x_1540_ == 0 {
                    leanh::lean_dec(v_stx_1537_);
                    v___x_1549_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_HeaderSyntax_imports___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Elab_HeaderSyntax_imports___closed__2_once),
                        _init_l_Lean_Elab_HeaderSyntax_imports___closed__2,
                    );
                    v___x_1550_ =
                        l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_1549_);
                    return v___x_1550_;
                } else {
                    v___x_1551_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1585_ = l_Lean_Syntax_getArg(v_stx_1537_, v___x_1551_);
                    v___x_1586_ = l_Lean_Syntax_isNone(v___x_1585_);
                    if v___x_1586_ == 0 {
                        v___x_1587_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1585_);
                        v___x_1588_ = l_Lean_Syntax_matchesNull(v___x_1585_, v___x_1587_);
                        if v___x_1588_ == 0 {
                            leanh::lean_dec(v___x_1585_);
                            leanh::lean_dec(v_stx_1537_);
                            v___x_1589_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_HeaderSyntax_imports___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_HeaderSyntax_imports___closed__2_once
                                ),
                                _init_l_Lean_Elab_HeaderSyntax_imports___closed__2,
                            );
                            v___x_1590_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(
                                v___x_1589_,
                            );
                            return v___x_1590_;
                        } else {
                            v___x_1591_ = l_Lean_Syntax_getArg(v___x_1585_, v___x_1551_);
                            leanh::lean_dec(v___x_1585_);
                            v___x_1592_ = l_Lean_Elab_HeaderSyntax_imports___closed__9;
                            leanh::lean_inc(v___x_1591_);
                            v___x_1593_ = l_Lean_Syntax_isOfKind(v___x_1591_, v___x_1592_);
                            if v___x_1593_ == 0 {
                                leanh::lean_dec(v___x_1591_);
                                leanh::lean_dec(v_stx_1537_);
                                v___x_1594_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_HeaderSyntax_imports___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_HeaderSyntax_imports___closed__2_once
                                    ),
                                    _init_l_Lean_Elab_HeaderSyntax_imports___closed__2,
                                );
                                v___x_1595_ =
                                    l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(
                                        v___x_1594_,
                                    );
                                return v___x_1595_;
                            } else {
                                v_moduleTk_1596_ = l_Lean_Syntax_getArg(v___x_1591_, v___x_1551_);
                                leanh::lean_dec(v___x_1591_);
                                v___x_1597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1597_, 0, v_moduleTk_1596_);
                                v_moduleTk_1570_ = v___x_1597_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1585_);
                        v___x_1598_ = leanh::lean_box(0);
                        v_moduleTk_1570_ = v___x_1598_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1545_ = lean_array_size(v___y_1542_);
                v___x_1546_ = 0usize;
                v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2(v___y_1543_, v___x_1540_, v_sz_1545_, v___x_1546_, v___y_1542_);
                leanh::lean_dec(v___y_1543_);
                v___x_1548_ = l_Array_append___redArg(v___y_1544_, v___x_1547_);
                leanh::lean_dec_ref(v___x_1547_);
                return v___x_1548_;
            }
            2 => {
                v___x_1555_ = l_Lean_Elab_HeaderSyntax_imports___closed__3;
                v___y_1542_ = v___y_1553_;
                v___y_1543_ = v___y_1554_;
                v___y_1544_ = v___x_1555_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1559_ = leanh::lean_unsigned_to_nat(2);
                v___x_1560_ = l_Lean_Syntax_getArg(v_stx_1537_, v___x_1559_);
                leanh::lean_dec(v_stx_1537_);
                v_importsStx_1561_ = l_Lean_Syntax_getArgs(v___x_1560_);
                leanh::lean_dec(v___x_1560_);
                if leanh::lean_obj_tag(v_preludeTk_1558_) == 0 {
                    if v___x_1540_ == 0 {
                        v___y_1553_ = v_importsStx_1561_;
                        v___y_1554_ = v___y_1557_;
                        state = 2;
                        continue;
                    } else {
                        if v_includeInit_1538_ == 0 {
                            v___y_1553_ = v_importsStx_1561_;
                            v___y_1554_ = v___y_1557_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1562_ = l_Lean_Elab_HeaderSyntax_imports___closed__5;
                            v___x_1563_ = 0;
                            v___x_1564_ = leanh::lean_alloc_ctor(0, 1, (3) as u32);
                            leanh::lean_ctor_set(v___x_1564_, 0, v___x_1562_);
                            leanh::lean_ctor_set_uint8(
                                v___x_1564_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_1563_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_1564_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1)
                                    as u32,
                                v___x_1540_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_1564_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2)
                                    as u32,
                                v___x_1563_,
                            );
                            v___x_1565_ = leanh::lean_alloc_ctor(0, 1, (3) as u32);
                            leanh::lean_ctor_set(v___x_1565_, 0, v___x_1562_);
                            leanh::lean_ctor_set_uint8(
                                v___x_1565_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_1563_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_1565_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1)
                                    as u32,
                                v___x_1540_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_1565_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2)
                                    as u32,
                                v___x_1540_,
                            );
                            v___x_1566_ = lean_mk_empty_array_with_capacity(v___x_1559_);
                            v___x_1567_ = lean_array_push(v___x_1566_, v___x_1564_);
                            v___x_1568_ = lean_array_push(v___x_1567_, v___x_1565_);
                            v___y_1542_ = v_importsStx_1561_;
                            v___y_1543_ = v___y_1557_;
                            v___y_1544_ = v___x_1568_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_preludeTk_1558_, 1);
                    v___y_1553_ = v_importsStx_1561_;
                    v___y_1554_ = v___y_1557_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1571_ = leanh::lean_unsigned_to_nat(1);
                v___x_1572_ = l_Lean_Syntax_getArg(v_stx_1537_, v___x_1571_);
                v___x_1573_ = l_Lean_Syntax_isNone(v___x_1572_);
                if v___x_1573_ == 0 {
                    leanh::lean_inc(v___x_1572_);
                    v___x_1574_ = l_Lean_Syntax_matchesNull(v___x_1572_, v___x_1571_);
                    if v___x_1574_ == 0 {
                        leanh::lean_dec(v___x_1572_);
                        leanh::lean_dec(v_moduleTk_1570_);
                        leanh::lean_dec(v_stx_1537_);
                        v___x_1575_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_HeaderSyntax_imports___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_HeaderSyntax_imports___closed__2_once
                            ),
                            _init_l_Lean_Elab_HeaderSyntax_imports___closed__2,
                        );
                        v___x_1576_ =
                            l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(v___x_1575_);
                        return v___x_1576_;
                    } else {
                        v___x_1577_ = l_Lean_Syntax_getArg(v___x_1572_, v___x_1551_);
                        leanh::lean_dec(v___x_1572_);
                        v___x_1578_ = l_Lean_Elab_HeaderSyntax_imports___closed__7;
                        leanh::lean_inc(v___x_1577_);
                        v___x_1579_ = l_Lean_Syntax_isOfKind(v___x_1577_, v___x_1578_);
                        if v___x_1579_ == 0 {
                            leanh::lean_dec(v___x_1577_);
                            leanh::lean_dec(v_moduleTk_1570_);
                            leanh::lean_dec(v_stx_1537_);
                            v___x_1580_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_HeaderSyntax_imports___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_HeaderSyntax_imports___closed__2_once
                                ),
                                _init_l_Lean_Elab_HeaderSyntax_imports___closed__2,
                            );
                            v___x_1581_ = l_panic___at___00Lean_Elab_HeaderSyntax_imports_spec__0(
                                v___x_1580_,
                            );
                            return v___x_1581_;
                        } else {
                            v_preludeTk_1582_ = l_Lean_Syntax_getArg(v___x_1577_, v___x_1551_);
                            leanh::lean_dec(v___x_1577_);
                            v___x_1583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1583_, 0, v_preludeTk_1582_);
                            v___y_1557_ = v_moduleTk_1570_;
                            v_preludeTk_1558_ = v___x_1583_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1572_);
                    v___x_1584_ = leanh::lean_box(0);
                    v___y_1557_ = v_moduleTk_1570_;
                    v_preludeTk_1558_ = v___x_1584_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_imports___boxed(
    mut v_stx_1599_: *mut leanh::LeanObject,
    mut v_includeInit_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeInit_boxed_1601_: u8 = 0;
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeInit_boxed_1601_ = (leanh::lean_unbox(v_includeInit_1600_) as u8);
    v_res_1602_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_1599_, v_includeInit_boxed_1601_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_Elab_HeaderSyntax_toModuleHeader(
    mut v_stx_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = 1;
    leanh::lean_inc(v_stx_1603_);
    v___x_1605_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_1603_, v___x_1604_);
    v___x_1606_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_1603_);
    leanh::lean_dec(v_stx_1603_);
    v___x_1607_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1607_, 0, v___x_1605_);
    leanh::lean_ctor_set_uint8(
        v___x_1607_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1606_,
    );
    return v___x_1607_;
}
pub unsafe fn l_Lean_Elab_headerToImports(
    mut v_stx_1608_: *mut leanh::LeanObject,
    mut v_includeInit_1609_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_1608_, v_includeInit_1609_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_Elab_headerToImports___boxed(
    mut v_stx_1611_: *mut leanh::LeanObject,
    mut v_includeInit_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_includeInit_boxed_1613_: u8 = 0;
    let mut v_res_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_includeInit_boxed_1613_ = (leanh::lean_unbox(v_includeInit_1612_) as u8);
    v_res_1614_ = l_Lean_Elab_headerToImports(v_stx_1611_, v_includeInit_boxed_1613_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(
    mut v_opts_1615_: *mut leanh::LeanObject,
    mut v_opt_1616_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1617_ = leanh::lean_ctor_get(v_opt_1616_, 0);
    v_defValue_1618_ = leanh::lean_ctor_get(v_opt_1616_, 1);
    v_map_1619_ = leanh::lean_ctor_get(v_opts_1615_, 0);
    v___x_1620_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1619_,
            v_name_1617_,
        );
    if leanh::lean_obj_tag(v___x_1620_) == 0 {
        let mut v___x_1621_: u8 = 0;
        v___x_1621_ = (leanh::lean_unbox(v_defValue_1618_) as u8);
        return v___x_1621_;
    } else {
        let mut v_val_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1622_ = leanh::lean_ctor_get(v___x_1620_, 0);
        leanh::lean_inc(v_val_1622_);
        leanh::lean_dec_ref_known(v___x_1620_, 1);
        if leanh::lean_obj_tag(v_val_1622_) == 1 {
            let mut v_v_1623_: u8 = 0;
            v_v_1623_ = leanh::lean_ctor_get_uint8(v_val_1622_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1622_, 0);
            return v_v_1623_;
        } else {
            let mut v___x_1624_: u8 = 0;
            leanh::lean_dec(v_val_1622_);
            v___x_1624_ = (leanh::lean_unbox(v_defValue_1618_) as u8);
            return v___x_1624_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0___boxed(
    mut v_opts_1625_: *mut leanh::LeanObject,
    mut v_opt_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1627_: u8 = 0;
    let mut v_r_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(
        v_opts_1625_,
        v_opt_1626_,
    );
    leanh::lean_dec_ref(v_opt_1626_);
    leanh::lean_dec_ref(v_opts_1625_);
    v_r_1628_ = leanh::lean_box((v_res_1627_) as usize);
    return v_r_1628_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(
    mut v_s_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_b_1631_: u8,
) -> u8 {
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v_pos_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v_str_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_needle_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v_str_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1670_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1672_: u8 = 0;
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v_nextStackPos_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1632_ = 0;
                match leanh::lean_obj_tag(v_a_1630_) {
                    0 => {
                        leanh::lean_dec_ref_known(v_a_1630_, 1);
                        v___x_1633_ = 1;
                        return v___x_1633_;
                    }
                    1 => {
                        v_pos_1634_ = leanh::lean_ctor_get(v_a_1630_, 0);
                        v_isSharedCheck_1647_ = (!leanh::lean_is_exclusive(v_a_1630_)) as u8;
                        if v_isSharedCheck_1647_ == 0 {
                            v___x_1636_ = v_a_1630_;
                            v_isShared_1637_ = v_isSharedCheck_1647_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_1634_);
                            leanh::lean_dec(v_a_1630_);
                            v___x_1636_ = leanh::lean_box(0);
                            v_isShared_1637_ = v_isSharedCheck_1647_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_1648_ = leanh::lean_ctor_get(v_a_1630_, 0);
                        v_table_1649_ = leanh::lean_ctor_get(v_a_1630_, 1);
                        v_stackPos_1650_ = leanh::lean_ctor_get(v_a_1630_, 2);
                        v_needlePos_1651_ = leanh::lean_ctor_get(v_a_1630_, 3);
                        v_isSharedCheck_1704_ = (!leanh::lean_is_exclusive(v_a_1630_)) as u8;
                        if v_isSharedCheck_1704_ == 0 {
                            v___x_1653_ = v_a_1630_;
                            v_isShared_1654_ = v_isSharedCheck_1704_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_needlePos_1651_);
                            leanh::lean_inc(v_stackPos_1650_);
                            leanh::lean_inc(v_table_1649_);
                            leanh::lean_inc(v_needle_1648_);
                            leanh::lean_dec(v_a_1630_);
                            v___x_1653_ = leanh::lean_box(0);
                            v_isShared_1654_ = v_isSharedCheck_1704_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        return v_b_1631_;
                    }
                }
            }
            1 => {
                v_str_1638_ = leanh::lean_ctor_get(v_s_1629_, 0);
                v_startInclusive_1639_ = leanh::lean_ctor_get(v_s_1629_, 1);
                v___x_1640_ = lean_nat_add(v_startInclusive_1639_, v_pos_1634_);
                leanh::lean_dec(v_pos_1634_);
                v___x_1641_ = lean_string_utf8_next_fast(v_str_1638_, v___x_1640_);
                leanh::lean_dec(v___x_1640_);
                v___x_1642_ = lean_nat_sub(v___x_1641_, v_startInclusive_1639_);
                if v_isShared_1637_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1636_, 0);
                    leanh::lean_ctor_set(v___x_1636_, 0, v___x_1642_);
                    v___x_1644_ = v___x_1636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1642_);
                    v___x_1644_ = v_reuseFailAlloc_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1630_ = v___x_1644_;
                v_b_1631_ = v___x_1632_;
                state = 0;
                continue;
            }
            3 => {
                v_str_1655_ = leanh::lean_ctor_get(v_needle_1648_, 0);
                v_startInclusive_1656_ = leanh::lean_ctor_get(v_needle_1648_, 1);
                v_endExclusive_1657_ = leanh::lean_ctor_get(v_needle_1648_, 2);
                v_str_1658_ = leanh::lean_ctor_get(v_s_1629_, 0);
                v_startInclusive_1659_ = leanh::lean_ctor_get(v_s_1629_, 1);
                v_endExclusive_1660_ = leanh::lean_ctor_get(v_s_1629_, 2);
                v_basePos_1661_ = lean_nat_sub(v_stackPos_1650_, v_needlePos_1651_);
                v___x_1662_ = lean_nat_sub(v_endExclusive_1657_, v_startInclusive_1656_);
                v___x_1663_ = lean_nat_add(v_basePos_1661_, v___x_1662_);
                v___x_1664_ = lean_nat_sub(v_endExclusive_1660_, v_startInclusive_1659_);
                v___x_1665_ = lean_nat_dec_le(v___x_1663_, v___x_1664_);
                leanh::lean_dec(v___x_1663_);
                if v___x_1665_ == 0 {
                    leanh::lean_dec(v___x_1662_);
                    leanh::lean_del_object(v___x_1653_);
                    leanh::lean_dec(v_needlePos_1651_);
                    leanh::lean_dec(v_stackPos_1650_);
                    leanh::lean_dec_ref(v_table_1649_);
                    leanh::lean_dec_ref(v_needle_1648_);
                    v___x_1666_ = lean_nat_dec_lt(v_basePos_1661_, v___x_1664_);
                    leanh::lean_dec(v___x_1664_);
                    leanh::lean_dec(v_basePos_1661_);
                    if v___x_1666_ == 0 {
                        return v_b_1631_;
                    } else {
                        v___x_1667_ = leanh::lean_box(3);
                        v_a_1630_ = v___x_1667_;
                        v_b_1631_ = v___x_1632_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1664_);
                    leanh::lean_dec(v_basePos_1661_);
                    v___x_1669_ = lean_nat_add(v_startInclusive_1659_, v_stackPos_1650_);
                    v_stackByte_1670_ = lean_string_get_byte_fast(v_str_1658_, v___x_1669_);
                    v___x_1671_ = lean_nat_add(v_startInclusive_1656_, v_needlePos_1651_);
                    v_patByte_1672_ = lean_string_get_byte_fast(v_str_1655_, v___x_1671_);
                    v___x_1673_ = lean_uint8_dec_eq(v_stackByte_1670_, v_patByte_1672_);
                    if v___x_1673_ == 0 {
                        leanh::lean_dec(v___x_1662_);
                        v___x_1674_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1675_ = lean_nat_dec_eq(v_needlePos_1651_, v___x_1674_);
                        if v___x_1675_ == 0 {
                            v___x_1676_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1677_ = lean_nat_sub(v_needlePos_1651_, v___x_1676_);
                            leanh::lean_dec(v_needlePos_1651_);
                            v_newNeedlePos_1678_ =
                                lean_array_fget_borrowed(v_table_1649_, v___x_1677_);
                            leanh::lean_dec(v___x_1677_);
                            v___x_1679_ = lean_nat_dec_eq(v_newNeedlePos_1678_, v___x_1674_);
                            if v___x_1679_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_1678_);
                                if v_isShared_1654_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_1653_,
                                        3,
                                        v_newNeedlePos_1678_,
                                    );
                                    v___x_1681_ = v___x_1653_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1683_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1683_,
                                        0,
                                        v_needle_1648_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1683_,
                                        1,
                                        v_table_1649_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1683_,
                                        2,
                                        v_stackPos_1650_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1683_,
                                        3,
                                        v_newNeedlePos_1678_,
                                    );
                                    v___x_1681_ = v_reuseFailAlloc_1683_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1684_ =
                                    l_String_Slice_posGE___redArg(v_s_1629_, v_stackPos_1650_);
                                if v_isShared_1654_ == 0 {
                                    leanh::lean_ctor_set(v___x_1653_, 3, v___x_1674_);
                                    leanh::lean_ctor_set(
                                        v___x_1653_,
                                        2,
                                        v_nextStackPos_1684_,
                                    );
                                    v___x_1686_ = v___x_1653_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1688_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1688_,
                                        0,
                                        v_needle_1648_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1688_,
                                        1,
                                        v_table_1649_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1688_,
                                        2,
                                        v_nextStackPos_1684_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1688_,
                                        3,
                                        v___x_1674_,
                                    );
                                    v___x_1686_ = v_reuseFailAlloc_1688_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_needlePos_1651_);
                            v___x_1689_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1690_ = lean_nat_add(v_stackPos_1650_, v___x_1689_);
                            leanh::lean_dec(v_stackPos_1650_);
                            v_nextStackPos_1691_ =
                                l_String_Slice_posGE___redArg(v_s_1629_, v___x_1690_);
                            if v_isShared_1654_ == 0 {
                                leanh::lean_ctor_set(v___x_1653_, 3, v___x_1674_);
                                leanh::lean_ctor_set(v___x_1653_, 2, v_nextStackPos_1691_);
                                v___x_1693_ = v___x_1653_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1695_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1695_,
                                    0,
                                    v_needle_1648_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1695_,
                                    1,
                                    v_table_1649_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1695_,
                                    2,
                                    v_nextStackPos_1691_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 3, v___x_1674_);
                                v___x_1693_ = v_reuseFailAlloc_1695_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_1696_ = leanh::lean_unsigned_to_nat(1);
                        v_nextNeedlePos_1697_ = lean_nat_add(v_needlePos_1651_, v___x_1696_);
                        leanh::lean_dec(v_needlePos_1651_);
                        v___x_1698_ = lean_nat_dec_eq(v_nextNeedlePos_1697_, v___x_1662_);
                        leanh::lean_dec(v___x_1662_);
                        if v___x_1698_ == 0 {
                            v_nextStackPos_1699_ = lean_nat_add(v_stackPos_1650_, v___x_1696_);
                            leanh::lean_dec(v_stackPos_1650_);
                            if v_isShared_1654_ == 0 {
                                leanh::lean_ctor_set(v___x_1653_, 3, v_nextNeedlePos_1697_);
                                leanh::lean_ctor_set(v___x_1653_, 2, v_nextStackPos_1699_);
                                v___x_1701_ = v___x_1653_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1703_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1703_,
                                    0,
                                    v_needle_1648_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1703_,
                                    1,
                                    v_table_1649_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1703_,
                                    2,
                                    v_nextStackPos_1699_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1703_,
                                    3,
                                    v_nextNeedlePos_1697_,
                                );
                                v___x_1701_ = v_reuseFailAlloc_1703_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_nextNeedlePos_1697_);
                            leanh::lean_del_object(v___x_1653_);
                            leanh::lean_dec(v_stackPos_1650_);
                            leanh::lean_dec_ref(v_table_1649_);
                            leanh::lean_dec_ref(v_needle_1648_);
                            return v___x_1698_;
                        }
                    }
                }
            }
            4 => {
                v_a_1630_ = v___x_1681_;
                v_b_1631_ = v___x_1632_;
                state = 0;
                continue;
            }
            5 => {
                v_a_1630_ = v___x_1686_;
                v_b_1631_ = v___x_1632_;
                state = 0;
                continue;
            }
            6 => {
                v_a_1630_ = v___x_1693_;
                v_b_1631_ = v___x_1632_;
                state = 0;
                continue;
            }
            7 => {
                v_a_1630_ = v___x_1701_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg___boxed(
    mut v_s_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_b_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1708_: u8 = 0;
    let mut v_res_1709_: u8 = 0;
    let mut v_r_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1708_ = (leanh::lean_unbox(v_b_1707_) as u8);
    v_res_1709_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_1705_, v_a_1706_, v_b_boxed_1708_);
    leanh::lean_dec_ref(v_s_1705_);
    v_r_1710_ = leanh::lean_box((v_res_1709_) as usize);
    return v_r_1710_;
}
pub unsafe fn _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ =
        l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0;
    v___x_1713_ = lean_string_utf8_byte_size(v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2()
-> u8 {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    v___x_1714_ = leanh::lean_unsigned_to_nat(0);
    v___x_1715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
    v___x_1716_ = lean_nat_dec_eq(v___x_1715_, v___x_1714_);
    return v___x_1716_;
}
pub unsafe fn _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__1);
    v___x_1718_ = leanh::lean_unsigned_to_nat(0);
    v___x_1719_ =
        l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__0;
    v___x_1720_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1720_, 0, v___x_1719_);
    leanh::lean_ctor_set(v___x_1720_, 1, v___x_1718_);
    leanh::lean_ctor_set(v___x_1720_, 2, v___x_1717_);
    return v___x_1720_;
}
pub unsafe fn _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
    v___x_1722_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = leanh::lean_unsigned_to_nat(0);
    v___x_1724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__4);
    v___x_1725_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__3);
    v___x_1726_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1726_, 0, v___x_1725_);
    leanh::lean_ctor_set(v___x_1726_, 1, v___x_1724_);
    leanh::lean_ctor_set(v___x_1726_, 2, v___x_1723_);
    leanh::lean_ctor_set(v___x_1726_, 3, v___x_1723_);
    return v___x_1726_;
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(
    mut v_s_1729_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1734_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__2);
                if v___x_1734_ == 0 {
                    v___x_1735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5), core::ptr::addr_of_mut!(l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5_once), _init_l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__5);
                    v___y_1731_ = v___x_1735_;
                    state = 1;
                    continue;
                } else {
                    v___x_1736_ = l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___closed__6;
                    v___y_1731_ = v___x_1736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1732_ = 0;
                leanh::lean_inc(v___y_1731_);
                v___x_1733_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_1729_, v___y_1731_, v___x_1732_);
                return v___x_1733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2___boxed(
    mut v_s_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1738_: u8 = 0;
    let mut v_r_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1738_ =
        l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(v_s_1737_);
    leanh::lean_dec_ref(v_s_1737_);
    v_r_1739_ = leanh::lean_box((v_res_1738_) as usize);
    return v_r_1739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(
    mut v_as_1740_: *mut leanh::LeanObject,
    mut v_sz_1741_: usize,
    mut v_i_1742_: usize,
    mut v_b_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: usize = 0;
    let mut v___x_1747_: usize = 0;
    let mut v___x_1749_: u8 = 0;
    let mut v_a_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1749_ = lean_usize_dec_lt(v_i_1742_, v_sz_1741_);
                if v___x_1749_ == 0 {
                    return v_b_1743_;
                } else {
                    v_a_1750_ = lean_array_uget_borrowed(v_as_1740_, v_i_1742_);
                    v___x_1751_ = l_Lean_Syntax_getTrailing_x3f(v_a_1750_);
                    if leanh::lean_obj_tag(v___x_1751_) == 0 {
                        v_a_1745_ = v_b_1743_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1752_ = leanh::lean_ctor_get(v___x_1751_, 0);
                        leanh::lean_inc(v_val_1752_);
                        leanh::lean_dec_ref_known(v___x_1751_, 1);
                        v_str_1753_ = leanh::lean_ctor_get(v_val_1752_, 0);
                        v_startPos_1754_ = leanh::lean_ctor_get(v_val_1752_, 1);
                        v_stopPos_1755_ = leanh::lean_ctor_get(v_val_1752_, 2);
                        v_isSharedCheck_1798_ =
                            (!leanh::lean_is_exclusive(v_val_1752_)) as u8;
                        if v_isSharedCheck_1798_ == 0 {
                            v___x_1757_ = v_val_1752_;
                            v_isShared_1758_ = v_isSharedCheck_1798_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_stopPos_1755_);
                            leanh::lean_inc(v_startPos_1754_);
                            leanh::lean_inc(v_str_1753_);
                            leanh::lean_dec(v_val_1752_);
                            v___x_1757_ = leanh::lean_box(0);
                            v_isShared_1758_ = v_isSharedCheck_1798_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1746_ = 1usize;
                v___x_1747_ = lean_usize_add(v_i_1742_, v___x_1746_);
                v_i_1742_ = v___x_1747_;
                v_b_1743_ = v_a_1745_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1759_ = leanh::lean_unsigned_to_nat(0);
                v___x_1768_ =
                    lean_string_utf8_extract(v_str_1753_, v_startPos_1754_, v_stopPos_1755_);
                leanh::lean_dec(v_stopPos_1755_);
                leanh::lean_dec(v_startPos_1754_);
                leanh::lean_dec_ref(v_str_1753_);
                v___x_1769_ = lean_string_utf8_byte_size(v___x_1768_);
                if v_isShared_1758_ == 0 {
                    leanh::lean_ctor_set(v___x_1757_, 2, v___x_1769_);
                    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1759_);
                    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1768_);
                    v___x_1771_ = v___x_1757_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 2, v___x_1769_);
                    v___x_1771_ = v_reuseFailAlloc_1797_;
                    state = 4;
                    continue;
                }
            }
            3 => {
                v___x_1761_ = leanh::lean_unsigned_to_nat(5);
                v___x_1762_ = l_Lean_Syntax_getArg(v_a_1750_, v___x_1761_);
                v___x_1763_ = l_Lean_Syntax_matchesNull(v___x_1762_, v___x_1759_);
                if v___x_1763_ == 0 {
                    v_a_1745_ = v_b_1743_;
                    state = 1;
                    continue;
                } else {
                    v___x_1764_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1765_ = l_Lean_Syntax_getArg(v_a_1750_, v___x_1764_);
                    v___x_1766_ = l_Lean_TSyntax_getId(v___x_1765_);
                    leanh::lean_dec(v___x_1765_);
                    v___x_1767_ = l_Lean_NameSet_insert(v_b_1743_, v___x_1766_);
                    v_a_1745_ = v___x_1767_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_1772_ =
                    l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(
                        v___x_1771_,
                    );
                leanh::lean_dec_ref(v___x_1771_);
                if v___x_1772_ == 0 {
                    v_a_1745_ = v_b_1743_;
                    state = 1;
                    continue;
                } else {
                    v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__4;
                    leanh::lean_inc(v_a_1750_);
                    v___x_1774_ = l_Lean_Syntax_isOfKind(v_a_1750_, v___x_1773_);
                    if v___x_1774_ == 0 {
                        v_a_1745_ = v_b_1743_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1775_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1791_ = l_Lean_Syntax_getArg(v_a_1750_, v___x_1759_);
                        v___x_1792_ = l_Lean_Syntax_isNone(v___x_1791_);
                        if v___x_1792_ == 0 {
                            leanh::lean_inc(v___x_1791_);
                            v___x_1793_ = l_Lean_Syntax_matchesNull(v___x_1791_, v___x_1775_);
                            if v___x_1793_ == 0 {
                                leanh::lean_dec(v___x_1791_);
                                v_a_1745_ = v_b_1743_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1794_ = l_Lean_Syntax_getArg(v___x_1791_, v___x_1759_);
                                leanh::lean_dec(v___x_1791_);
                                v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__14;
                                v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
                                if v___x_1796_ == 0 {
                                    v_a_1745_ = v_b_1743_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1791_);
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_1777_ = leanh::lean_unsigned_to_nat(3);
                v___x_1778_ = l_Lean_Syntax_getArg(v_a_1750_, v___x_1777_);
                v___x_1779_ = l_Lean_Syntax_isNone(v___x_1778_);
                if v___x_1779_ == 0 {
                    leanh::lean_inc(v___x_1778_);
                    v___x_1780_ = l_Lean_Syntax_matchesNull(v___x_1778_, v___x_1775_);
                    if v___x_1780_ == 0 {
                        leanh::lean_dec(v___x_1778_);
                        v_a_1745_ = v_b_1743_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1781_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1759_);
                        leanh::lean_dec(v___x_1778_);
                        v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__10;
                        v___x_1783_ = l_Lean_Syntax_isOfKind(v___x_1781_, v___x_1782_);
                        if v___x_1783_ == 0 {
                            v_a_1745_ = v_b_1743_;
                            state = 1;
                            continue;
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1778_);
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_1785_ = l_Lean_Syntax_getArg(v_a_1750_, v___x_1775_);
                v___x_1786_ = l_Lean_Syntax_isNone(v___x_1785_);
                if v___x_1786_ == 0 {
                    leanh::lean_inc(v___x_1785_);
                    v___x_1787_ = l_Lean_Syntax_matchesNull(v___x_1785_, v___x_1775_);
                    if v___x_1787_ == 0 {
                        leanh::lean_dec(v___x_1785_);
                        v_a_1745_ = v_b_1743_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1788_ = l_Lean_Syntax_getArg(v___x_1785_, v___x_1759_);
                        leanh::lean_dec(v___x_1785_);
                        v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__12;
                        v___x_1790_ = l_Lean_Syntax_isOfKind(v___x_1788_, v___x_1789_);
                        if v___x_1790_ == 0 {
                            v_a_1745_ = v_b_1743_;
                            state = 1;
                            continue;
                        } else {
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1785_);
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3___boxed(
    mut v_as_1799_: *mut leanh::LeanObject,
    mut v_sz_1800_: *mut leanh::LeanObject,
    mut v_i_1801_: *mut leanh::LeanObject,
    mut v_b_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1803_: usize = 0;
    let mut v_i_boxed_1804_: usize = 0;
    let mut v_res_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1803_ = leanh::lean_unbox_usize(v_sz_1800_);
    leanh::lean_dec(v_sz_1800_);
    v_i_boxed_1804_ = leanh::lean_unbox_usize(v_i_1801_);
    leanh::lean_dec(v_i_1801_);
    v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v_as_1799_, v_sz_boxed_1803_, v_i_boxed_1804_, v_b_1802_);
    leanh::lean_dec_ref(v_as_1799_);
    return v_res_1805_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(
    mut v_o_1809_: *mut leanh::LeanObject,
    mut v_k_1810_: *mut leanh::LeanObject,
    mut v_v_1811_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1813_: u8 = 0;
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1812_ = leanh::lean_ctor_get(v_o_1809_, 0);
                v_hasTrace_1813_ = leanh::lean_ctor_get_uint8(
                    v_o_1809_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1827_ = (!leanh::lean_is_exclusive(v_o_1809_)) as u8;
                if v_isSharedCheck_1827_ == 0 {
                    v___x_1815_ = v_o_1809_;
                    v_isShared_1816_ = v_isSharedCheck_1827_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1812_);
                    leanh::lean_dec(v_o_1809_);
                    v___x_1815_ = leanh::lean_box(0);
                    v_isShared_1816_ = v_isSharedCheck_1827_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1817_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_1817_, 0 as u32, v_v_1811_);
                leanh::lean_inc(v_k_1810_);
                v___x_1818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1810_, v___x_1817_, v_map_1812_);
                if v_hasTrace_1813_ == 0 {
                    v___x_1819_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___closed__1;
                    v___x_1820_ = l_Lean_Name_isPrefixOf(v___x_1819_, v_k_1810_);
                    leanh::lean_dec(v_k_1810_);
                    if v_isShared_1816_ == 0 {
                        leanh::lean_ctor_set(v___x_1815_, 0, v___x_1818_);
                        v___x_1822_ = v___x_1815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1823_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1818_);
                        v___x_1822_ = v_reuseFailAlloc_1823_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1810_);
                    if v_isShared_1816_ == 0 {
                        leanh::lean_ctor_set(v___x_1815_, 0, v___x_1818_);
                        v___x_1825_ = v___x_1815_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1826_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1818_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1826_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1813_,
                        );
                        v___x_1825_ = v_reuseFailAlloc_1826_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1822_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1820_,
                );
                return v___x_1822_;
            }
            3 => {
                return v___x_1825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5___boxed(
    mut v_o_1828_: *mut leanh::LeanObject,
    mut v_k_1829_: *mut leanh::LeanObject,
    mut v_v_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1831_: u8 = 0;
    let mut v_res_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1831_ = (leanh::lean_unbox(v_v_1830_) as u8);
    v_res_1832_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_o_1828_, v_k_1829_, v_v_boxed_1831_);
    return v_res_1832_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(
    mut v_opts_1833_: *mut leanh::LeanObject,
    mut v_opt_1834_: *mut leanh::LeanObject,
    mut v_val_1835_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1836_ = leanh::lean_ctor_get(v_opt_1834_, 0);
    leanh::lean_inc(v_name_1836_);
    leanh::lean_dec_ref(v_opt_1834_);
    v___x_1837_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4_spec__5(v_opts_1833_, v_name_1836_, v_val_1835_);
    return v___x_1837_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4___boxed(
    mut v_opts_1838_: *mut leanh::LeanObject,
    mut v_opt_1839_: *mut leanh::LeanObject,
    mut v_val_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_1841_: u8 = 0;
    let mut v_res_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_1841_ = (leanh::lean_unbox(v_val_1840_) as u8);
    v_res_1842_ = l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(
        v_opts_1838_,
        v_opt_1839_,
        v_val_boxed_1841_,
    );
    return v_res_1842_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(
    mut v_ignoreDeprecatedImports_1848_: *mut leanh::LeanObject,
    mut v_env_1849_: *mut leanh::LeanObject,
    mut v_inputCtx_1850_: *mut leanh::LeanObject,
    mut v_startPos_1851_: *mut leanh::LeanObject,
    mut v_as_1852_: *mut leanh::LeanObject,
    mut v_i_1853_: usize,
    mut v_stop_1854_: usize,
    mut v_b_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: usize = 0;
    let mut v___x_1859_: usize = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1871_: u8 = 0;
    let mut v_fileName_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: u8 = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1861_ = lean_usize_dec_eq(v_i_1853_, v_stop_1854_);
                if v___x_1861_ == 0 {
                    v___x_1862_ = lean_array_uget_borrowed(v_as_1852_, v_i_1853_);
                    v_module_1863_ = leanh::lean_ctor_get(v___x_1862_, 0);
                    v___x_1864_ =
                        l_Lean_NameSet_contains(v_ignoreDeprecatedImports_1848_, v_module_1863_);
                    if v___x_1864_ == 0 {
                        v___x_1865_ =
                            l_Lean_Environment_getModuleIdx_x3f(v_env_1849_, v_module_1863_);
                        if leanh::lean_obj_tag(v___x_1865_) == 0 {
                            v___y_1857_ = v_b_1855_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1866_ = leanh::lean_ctor_get(v___x_1865_, 0);
                            leanh::lean_inc(v_val_1866_);
                            leanh::lean_dec_ref_known(v___x_1865_, 1);
                            v___x_1867_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(
                                v_env_1849_,
                                v_val_1866_,
                            );
                            if leanh::lean_obj_tag(v___x_1867_) == 0 {
                                leanh::lean_dec(v_val_1866_);
                                v___y_1857_ = v_b_1855_;
                                state = 1;
                                continue;
                            } else {
                                v_val_1868_ = leanh::lean_ctor_get(v___x_1867_, 0);
                                v_isSharedCheck_1887_ =
                                    (!leanh::lean_is_exclusive(v___x_1867_)) as u8;
                                if v_isSharedCheck_1887_ == 0 {
                                    v___x_1870_ = v___x_1867_;
                                    v_isShared_1871_ = v_isSharedCheck_1887_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1868_);
                                    leanh::lean_dec(v___x_1867_);
                                    v___x_1870_ = leanh::lean_box(0);
                                    v_isShared_1871_ = v_isSharedCheck_1887_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___y_1857_ = v_b_1855_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inputCtx_1850_);
                    return v_b_1855_;
                }
            }
            1 => {
                v___x_1858_ = 1usize;
                v___x_1859_ = lean_usize_add(v_i_1853_, v___x_1858_);
                v_i_1853_ = v___x_1859_;
                v_b_1855_ = v___y_1857_;
                state = 0;
                continue;
            }
            2 => {
                v_fileName_1872_ = leanh::lean_ctor_get(v_inputCtx_1850_, 1);
                v_fileMap_1873_ = leanh::lean_ctor_get(v_inputCtx_1850_, 2);
                leanh::lean_inc_ref(v_fileMap_1873_);
                v_pos_1874_ = l_Lean_FileMap_toPosition(v_fileMap_1873_, v_startPos_1851_);
                v___x_1875_ = leanh::lean_box(0);
                v___x_1876_ = 1;
                v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0;
                v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__2;
                leanh::lean_inc(v_module_1863_);
                v___x_1879_ = l_Lean_formatDeprecatedModuleWarning(
                    v_env_1849_,
                    v_val_1866_,
                    v_module_1863_,
                    v_val_1868_,
                );
                leanh::lean_dec(v_val_1866_);
                if v_isShared_1871_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1870_, 3);
                    leanh::lean_ctor_set(v___x_1870_, 0, v___x_1879_);
                    v___x_1881_ = v___x_1870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1886_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1879_);
                    v___x_1881_ = v_reuseFailAlloc_1886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1882_ = l_Lean_MessageData_ofFormat(v___x_1881_);
                v___x_1883_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1883_, 0, v___x_1878_);
                leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                leanh::lean_inc_ref(v_fileName_1872_);
                v___x_1884_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_1884_, 0, v_fileName_1872_);
                leanh::lean_ctor_set(v___x_1884_, 1, v_pos_1874_);
                leanh::lean_ctor_set(v___x_1884_, 2, v___x_1875_);
                leanh::lean_ctor_set(v___x_1884_, 3, v___x_1877_);
                leanh::lean_ctor_set(v___x_1884_, 4, v___x_1883_);
                leanh::lean_ctor_set_uint8(
                    v___x_1884_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_1864_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1884_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1876_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1884_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_1864_,
                );
                v___x_1885_ = l_Lean_MessageLog_add(v___x_1884_, v_b_1855_);
                v___y_1857_ = v___x_1885_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___boxed(
    mut v_ignoreDeprecatedImports_1888_: *mut leanh::LeanObject,
    mut v_env_1889_: *mut leanh::LeanObject,
    mut v_inputCtx_1890_: *mut leanh::LeanObject,
    mut v_startPos_1891_: *mut leanh::LeanObject,
    mut v_as_1892_: *mut leanh::LeanObject,
    mut v_i_1893_: *mut leanh::LeanObject,
    mut v_stop_1894_: *mut leanh::LeanObject,
    mut v_b_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1896_: usize = 0;
    let mut v_stop_boxed_1897_: usize = 0;
    let mut v_res_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1896_ = leanh::lean_unbox_usize(v_i_1893_);
    leanh::lean_dec(v_i_1893_);
    v_stop_boxed_1897_ = leanh::lean_unbox_usize(v_stop_1894_);
    leanh::lean_dec(v_stop_1894_);
    v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_1888_, v_env_1889_, v_inputCtx_1890_, v_startPos_1891_, v_as_1892_, v_i_boxed_1896_, v_stop_boxed_1897_, v_b_1895_);
    leanh::lean_dec_ref(v_as_1892_);
    leanh::lean_dec(v_startPos_1891_);
    leanh::lean_dec_ref(v_env_1889_);
    leanh::lean_dec(v_ignoreDeprecatedImports_1888_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedImports(
    mut v_env_1899_: *mut leanh::LeanObject,
    mut v_imports_1900_: *mut leanh::LeanObject,
    mut v_opts_1901_: *mut leanh::LeanObject,
    mut v_inputCtx_1902_: *mut leanh::LeanObject,
    mut v_startPos_1903_: *mut leanh::LeanObject,
    mut v_messages_1904_: *mut leanh::LeanObject,
    mut v_headerStx_x3f_1905_: *mut leanh::LeanObject,
    mut v_origHeaderStx_x3f_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_opts_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ignoreDeprecatedImports_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: usize = 0;
    let mut v___x_1917_: usize = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: usize = 0;
    let mut v___x_1920_: usize = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ignoreDeprecatedImports_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1926_: usize = 0;
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importsStx_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v_opts_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v___y_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleTk_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v_val_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v_moduleTk_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ignoreDeprecatedImports_1922_ = l_Lean_NameSet_empty;
                if leanh::lean_obj_tag(v_origHeaderStx_x3f_1906_) == 0 {
                    if leanh::lean_obj_tag(v_headerStx_x3f_1905_) == 1 {
                        v_val_1988_ = leanh::lean_ctor_get(v_headerStx_x3f_1905_, 0);
                        leanh::lean_inc(v_val_1988_);
                        leanh::lean_dec_ref_known(v_headerStx_x3f_1905_, 1);
                        v_val_1971_ = v_val_1988_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_headerStx_x3f_1905_);
                        v_opts_1908_ = v_opts_1901_;
                        v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_headerStx_x3f_1905_);
                    v_val_1989_ = leanh::lean_ctor_get(v_origHeaderStx_x3f_1906_, 0);
                    leanh::lean_inc(v_val_1989_);
                    leanh::lean_dec_ref_known(v_origHeaderStx_x3f_1906_, 1);
                    v_val_1971_ = v_val_1989_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = l_Lean_linter_deprecated_module;
                v___x_1911_ = l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(
                    v_opts_1908_,
                    v___x_1910_,
                );
                leanh::lean_dec_ref(v_opts_1908_);
                if v___x_1911_ == 0 {
                    leanh::lean_dec(v_ignoreDeprecatedImports_1909_);
                    leanh::lean_dec_ref(v_inputCtx_1902_);
                    return v_messages_1904_;
                } else {
                    v___x_1912_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1913_ = lean_array_get_size(v_imports_1900_);
                    v___x_1914_ = lean_nat_dec_lt(v___x_1912_, v___x_1913_);
                    if v___x_1914_ == 0 {
                        leanh::lean_dec(v_ignoreDeprecatedImports_1909_);
                        leanh::lean_dec_ref(v_inputCtx_1902_);
                        return v_messages_1904_;
                    } else {
                        v___x_1915_ = lean_nat_dec_le(v___x_1913_, v___x_1913_);
                        if v___x_1915_ == 0 {
                            if v___x_1914_ == 0 {
                                leanh::lean_dec(v_ignoreDeprecatedImports_1909_);
                                leanh::lean_dec_ref(v_inputCtx_1902_);
                                return v_messages_1904_;
                            } else {
                                v___x_1916_ = 0usize;
                                v___x_1917_ = lean_usize_of_nat(v___x_1913_);
                                v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_1909_, v_env_1899_, v_inputCtx_1902_, v_startPos_1903_, v_imports_1900_, v___x_1916_, v___x_1917_, v_messages_1904_);
                                leanh::lean_dec(v_ignoreDeprecatedImports_1909_);
                                return v___x_1918_;
                            }
                        } else {
                            v___x_1919_ = 0usize;
                            v___x_1920_ = lean_usize_of_nat(v___x_1913_);
                            v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1(v_ignoreDeprecatedImports_1909_, v_env_1899_, v_inputCtx_1902_, v_startPos_1903_, v_imports_1900_, v___x_1919_, v___x_1920_, v_messages_1904_);
                            leanh::lean_dec(v_ignoreDeprecatedImports_1909_);
                            return v___x_1921_;
                        }
                    }
                }
            }
            2 => {
                v_sz_1926_ = lean_array_size(v___y_1924_);
                v___x_1927_ = 0usize;
                v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_checkDeprecatedImports_spec__3(v___y_1924_, v_sz_1926_, v___x_1927_, v_ignoreDeprecatedImports_1922_);
                leanh::lean_dec_ref(v___y_1924_);
                v_opts_1908_ = v_opts_1925_;
                v_ignoreDeprecatedImports_1909_ = v___x_1928_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1933_ = leanh::lean_unsigned_to_nat(2);
                v___x_1934_ = l_Lean_Syntax_getArg(v___y_1932_, v___x_1933_);
                leanh::lean_dec(v___y_1932_);
                v_importsStx_1935_ = l_Lean_Syntax_getArgs(v___x_1934_);
                leanh::lean_dec(v___x_1934_);
                if leanh::lean_obj_tag(v___y_1931_) == 0 {
                    leanh::lean_dec(v___y_1930_);
                    v___y_1924_ = v_importsStx_1935_;
                    v_opts_1925_ = v_opts_1901_;
                    state = 2;
                    continue;
                } else {
                    v_val_1936_ = leanh::lean_ctor_get(v___y_1931_, 0);
                    leanh::lean_inc(v_val_1936_);
                    leanh::lean_dec_ref_known(v___y_1931_, 1);
                    v___x_1937_ = l_Lean_Syntax_getTrailing_x3f(v_val_1936_);
                    leanh::lean_dec(v_val_1936_);
                    if leanh::lean_obj_tag(v___x_1937_) == 0 {
                        leanh::lean_dec(v___y_1930_);
                        v___y_1924_ = v_importsStx_1935_;
                        v_opts_1925_ = v_opts_1901_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1938_ = leanh::lean_ctor_get(v___x_1937_, 0);
                        leanh::lean_inc(v_val_1938_);
                        leanh::lean_dec_ref_known(v___x_1937_, 1);
                        v_str_1939_ = leanh::lean_ctor_get(v_val_1938_, 0);
                        v_startPos_1940_ = leanh::lean_ctor_get(v_val_1938_, 1);
                        v_stopPos_1941_ = leanh::lean_ctor_get(v_val_1938_, 2);
                        v_isSharedCheck_1954_ =
                            (!leanh::lean_is_exclusive(v_val_1938_)) as u8;
                        if v_isSharedCheck_1954_ == 0 {
                            v___x_1943_ = v_val_1938_;
                            v_isShared_1944_ = v_isSharedCheck_1954_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_stopPos_1941_);
                            leanh::lean_inc(v_startPos_1940_);
                            leanh::lean_inc(v_str_1939_);
                            leanh::lean_dec(v_val_1938_);
                            v___x_1943_ = leanh::lean_box(0);
                            v_isShared_1944_ = v_isSharedCheck_1954_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1945_ =
                    lean_string_utf8_extract(v_str_1939_, v_startPos_1940_, v_stopPos_1941_);
                leanh::lean_dec(v_stopPos_1941_);
                leanh::lean_dec(v_startPos_1940_);
                leanh::lean_dec_ref(v_str_1939_);
                v___x_1946_ = lean_string_utf8_byte_size(v___x_1945_);
                if v_isShared_1944_ == 0 {
                    leanh::lean_ctor_set(v___x_1943_, 2, v___x_1946_);
                    leanh::lean_ctor_set(v___x_1943_, 1, v___y_1930_);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1945_);
                    v___x_1948_ = v___x_1943_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___y_1930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1946_);
                    v___x_1948_ = v_reuseFailAlloc_1953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1949_ =
                    l_String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2(
                        v___x_1948_,
                    );
                leanh::lean_dec_ref(v___x_1948_);
                if v___x_1949_ == 0 {
                    v___y_1924_ = v_importsStx_1935_;
                    v_opts_1925_ = v_opts_1901_;
                    state = 2;
                    continue;
                } else {
                    v___x_1950_ = l_Lean_linter_deprecated_module;
                    v___x_1951_ = 0;
                    v_opts_1952_ =
                        l_Lean_Option_set___at___00Lean_Elab_checkDeprecatedImports_spec__4(
                            v_opts_1901_,
                            v___x_1950_,
                            v___x_1951_,
                        );
                    v___y_1924_ = v_importsStx_1935_;
                    v_opts_1925_ = v_opts_1952_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_1962_ = leanh::lean_unsigned_to_nat(1);
                v___x_1963_ = l_Lean_Syntax_getArg(v___y_1960_, v___x_1962_);
                v___x_1964_ = l_Lean_Syntax_isNone(v___x_1963_);
                if v___x_1964_ == 0 {
                    leanh::lean_inc(v___x_1963_);
                    v___x_1965_ = l_Lean_Syntax_matchesNull(v___x_1963_, v___x_1962_);
                    if v___x_1965_ == 0 {
                        leanh::lean_dec(v___x_1963_);
                        leanh::lean_dec(v_moduleTk_1961_);
                        leanh::lean_dec(v___y_1960_);
                        leanh::lean_dec(v___y_1959_);
                        v_opts_1908_ = v_opts_1901_;
                        v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1966_ = l_Lean_Syntax_getArg(v___x_1963_, v___y_1959_);
                        leanh::lean_dec(v___x_1963_);
                        v___x_1967_ = l_Lean_Elab_HeaderSyntax_imports___closed__6;
                        leanh::lean_inc_ref(v___y_1958_);
                        leanh::lean_inc_ref(v___y_1957_);
                        leanh::lean_inc_ref(v___y_1956_);
                        v___x_1968_ =
                            l_Lean_Name_mkStr4(v___y_1956_, v___y_1957_, v___y_1958_, v___x_1967_);
                        v___x_1969_ = l_Lean_Syntax_isOfKind(v___x_1966_, v___x_1968_);
                        leanh::lean_dec(v___x_1968_);
                        if v___x_1969_ == 0 {
                            leanh::lean_dec(v_moduleTk_1961_);
                            leanh::lean_dec(v___y_1960_);
                            leanh::lean_dec(v___y_1959_);
                            v_opts_1908_ = v_opts_1901_;
                            v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                            state = 1;
                            continue;
                        } else {
                            v___y_1930_ = v___y_1959_;
                            v___y_1931_ = v_moduleTk_1961_;
                            v___y_1932_ = v___y_1960_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1963_);
                    v___y_1930_ = v___y_1959_;
                    v___y_1931_ = v_moduleTk_1961_;
                    v___y_1932_ = v___y_1960_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__0;
                v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__1;
                v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_HeaderSyntax_imports_spec__2___closed__2;
                v___x_1975_ = l_Lean_Elab_HeaderSyntax_imports___closed__1;
                leanh::lean_inc(v_val_1971_);
                v___x_1976_ = l_Lean_Syntax_isOfKind(v_val_1971_, v___x_1975_);
                if v___x_1976_ == 0 {
                    leanh::lean_dec(v_val_1971_);
                    v_opts_1908_ = v_opts_1901_;
                    v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                    state = 1;
                    continue;
                } else {
                    v___x_1977_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1978_ = l_Lean_Syntax_getArg(v_val_1971_, v___x_1977_);
                    v___x_1979_ = l_Lean_Syntax_isNone(v___x_1978_);
                    if v___x_1979_ == 0 {
                        v___x_1980_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1978_);
                        v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1978_, v___x_1980_);
                        if v___x_1981_ == 0 {
                            leanh::lean_dec(v___x_1978_);
                            leanh::lean_dec(v_val_1971_);
                            v_opts_1908_ = v_opts_1901_;
                            v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1982_ = l_Lean_Syntax_getArg(v___x_1978_, v___x_1977_);
                            leanh::lean_dec(v___x_1978_);
                            v___x_1983_ = l_Lean_Elab_HeaderSyntax_imports___closed__9;
                            leanh::lean_inc(v___x_1982_);
                            v___x_1984_ = l_Lean_Syntax_isOfKind(v___x_1982_, v___x_1983_);
                            if v___x_1984_ == 0 {
                                leanh::lean_dec(v___x_1982_);
                                leanh::lean_dec(v_val_1971_);
                                v_opts_1908_ = v_opts_1901_;
                                v_ignoreDeprecatedImports_1909_ = v_ignoreDeprecatedImports_1922_;
                                state = 1;
                                continue;
                            } else {
                                v_moduleTk_1985_ = l_Lean_Syntax_getArg(v___x_1982_, v___x_1977_);
                                leanh::lean_dec(v___x_1982_);
                                v___x_1986_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1986_, 0, v_moduleTk_1985_);
                                v___y_1956_ = v___x_1972_;
                                v___y_1957_ = v___x_1973_;
                                v___y_1958_ = v___x_1974_;
                                v___y_1959_ = v___x_1977_;
                                v___y_1960_ = v_val_1971_;
                                v_moduleTk_1961_ = v___x_1986_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1978_);
                        v___x_1987_ = leanh::lean_box(0);
                        v___y_1956_ = v___x_1972_;
                        v___y_1957_ = v___x_1973_;
                        v___y_1958_ = v___x_1974_;
                        v___y_1959_ = v___x_1977_;
                        v___y_1960_ = v_val_1971_;
                        v_moduleTk_1961_ = v___x_1987_;
                        state = 6;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkDeprecatedImports___boxed(
    mut v_env_1990_: *mut leanh::LeanObject,
    mut v_imports_1991_: *mut leanh::LeanObject,
    mut v_opts_1992_: *mut leanh::LeanObject,
    mut v_inputCtx_1993_: *mut leanh::LeanObject,
    mut v_startPos_1994_: *mut leanh::LeanObject,
    mut v_messages_1995_: *mut leanh::LeanObject,
    mut v_headerStx_x3f_1996_: *mut leanh::LeanObject,
    mut v_origHeaderStx_x3f_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_Elab_checkDeprecatedImports(
        v_env_1990_,
        v_imports_1991_,
        v_opts_1992_,
        v_inputCtx_1993_,
        v_startPos_1994_,
        v_messages_1995_,
        v_headerStx_x3f_1996_,
        v_origHeaderStx_x3f_1997_,
    );
    leanh::lean_dec(v_startPos_1994_);
    leanh::lean_dec_ref(v_imports_1991_);
    leanh::lean_dec_ref(v_env_1990_);
    return v_res_1998_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(
    mut v_s_1999_: *mut leanh::LeanObject,
    mut v_inst_2000_: *mut leanh::LeanObject,
    mut v_R_2001_: *mut leanh::LeanObject,
    mut v_a_2002_: *mut leanh::LeanObject,
    mut v_b_2003_: u8,
    mut v_c_2004_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2005_: u8 = 0;
    v___x_2005_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___redArg(v_s_1999_, v_a_2002_, v_b_2003_);
    return v___x_2005_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2___boxed(
    mut v_s_2006_: *mut leanh::LeanObject,
    mut v_inst_2007_: *mut leanh::LeanObject,
    mut v_R_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_b_2010_: *mut leanh::LeanObject,
    mut v_c_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_2012_: u8 = 0;
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2012_ = (leanh::lean_unbox(v_b_2010_) as u8);
    v_res_2013_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Elab_checkDeprecatedImports_spec__2_spec__2(v_s_2006_, v_inst_2007_, v_R_2008_, v_a_2009_, v_b_boxed_2012_, v_c_2011_);
    leanh::lean_dec_ref(v_s_2006_);
    v_r_2014_ = leanh::lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_2015_: u32 = 0;
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = 33;
    v___x_2016_ = leanh::lean_box_uint32(v___x_2015_);
    return v___x_2016_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2()
-> *mut leanh::LeanObject {
    let mut v___x_2017_: u32 = 0;
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = 42;
    v___x_2018_ = leanh::lean_box_uint32(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3()
-> *mut leanh::LeanObject {
    let mut v___x_2019_: u32 = 0;
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = 63;
    v___x_2020_ = leanh::lean_box_uint32(v___x_2019_);
    return v___x_2020_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4()
-> *mut leanh::LeanObject {
    let mut v___x_2021_: u32 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2021_ = 124;
    v___x_2022_ = leanh::lean_box_uint32(v___x_2021_);
    return v___x_2022_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5()
-> *mut leanh::LeanObject {
    let mut v___x_2023_: u32 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ = 34;
    v___x_2024_ = leanh::lean_box_uint32(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6()
-> *mut leanh::LeanObject {
    let mut v___x_2025_: u32 = 0;
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = 62;
    v___x_2026_ = leanh::lean_box_uint32(v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7()
-> *mut leanh::LeanObject {
    let mut v___x_2027_: u32 = 0;
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = 60;
    v___x_2028_ = leanh::lean_box_uint32(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = leanh::lean_unsigned_to_nat(7);
    v___x_2030_ = lean_mk_empty_array_with_capacity(v___x_2029_);
    v___x_2031_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7;
    v___x_2032_ = lean_array_push(v___x_2030_, v___x_2031_);
    v___x_2033_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6;
    v___x_2034_ = lean_array_push(v___x_2032_, v___x_2033_);
    v___x_2035_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5;
    v___x_2036_ = lean_array_push(v___x_2034_, v___x_2035_);
    v___x_2037_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4;
    v___x_2038_ = lean_array_push(v___x_2036_, v___x_2037_);
    v___x_2039_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3;
    v___x_2040_ = lean_array_push(v___x_2038_, v___x_2039_);
    v___x_2041_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2;
    v___x_2042_ = lean_array_push(v___x_2040_, v___x_2041_);
    v___x_2043_ =
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1;
    v___x_2044_ = lean_array_push(v___x_2042_, v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars()
-> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0_once
        ),
        _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0,
    );
    return v___x_2045_;
}
pub unsafe fn l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(
    mut v_s_2133_: *mut leanh::LeanObject,
    mut v_p_2134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2136_: u32 = 0;
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: u8 = 0;
    let mut v___x_2143_: u32 = 0;
    let mut v___x_2144_: u32 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: u32 = 0;
    let mut v___x_2147_: u8 = 0;
    let mut v___x_2148_: u32 = 0;
    let mut v___x_2149_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2141_ = lean_string_utf8_byte_size(v_s_2133_);
                v___x_2142_ = lean_nat_dec_eq(v_p_2134_, v___x_2141_);
                if v___x_2142_ == 0 {
                    v___x_2143_ = lean_string_utf8_get_fast(v_s_2133_, v_p_2134_);
                    v___x_2144_ = 97;
                    v___x_2145_ = lean_uint32_dec_le(v___x_2144_, v___x_2143_);
                    if v___x_2145_ == 0 {
                        v___y_2136_ = v___x_2143_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2146_ = 122;
                        v___x_2147_ = lean_uint32_dec_le(v___x_2143_, v___x_2146_);
                        if v___x_2147_ == 0 {
                            v___y_2136_ = v___x_2143_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2148_ = 4294967264;
                            v___x_2149_ = lean_uint32_add(v___x_2143_, v___x_2148_);
                            v___y_2136_ = v___x_2149_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_p_2134_);
                    return v_s_2133_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_2134_);
                v___x_2137_ = lean_string_utf8_set(v_s_2133_, v_p_2134_, v___y_2136_);
                v___x_2138_ = l_Char_utf8Size(v___y_2136_);
                v___x_2139_ = lean_nat_add(v_p_2134_, v___x_2138_);
                leanh::lean_dec(v___x_2138_);
                leanh::lean_dec(v_p_2134_);
                v_s_2133_ = v___x_2137_;
                v_p_2134_ = v___x_2139_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(
    mut v_s_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: u32,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_b_2153_: u8,
) -> u8 {
    let mut v_str_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u32 = 0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2154_ = leanh::lean_ctor_get(v_s_2150_, 0);
                v_startInclusive_2155_ = leanh::lean_ctor_get(v_s_2150_, 1);
                v_endExclusive_2156_ = leanh::lean_ctor_get(v_s_2150_, 2);
                v___x_2157_ = lean_nat_sub(v_endExclusive_2156_, v_startInclusive_2155_);
                v___x_2158_ = lean_nat_dec_eq(v_a_2152_, v___x_2157_);
                leanh::lean_dec(v___x_2157_);
                if v___x_2158_ == 0 {
                    v___x_2159_ = lean_nat_add(v_startInclusive_2155_, v_a_2152_);
                    leanh::lean_dec(v_a_2152_);
                    v___x_2160_ = lean_string_utf8_get_fast(v_str_2154_, v___x_2159_);
                    v___x_2161_ = lean_uint32_dec_eq(v___x_2160_, v_a_2151_);
                    if v___x_2161_ == 0 {
                        v___x_2162_ = lean_string_utf8_next_fast(v_str_2154_, v___x_2159_);
                        leanh::lean_dec(v___x_2159_);
                        v___x_2163_ = lean_nat_sub(v___x_2162_, v_startInclusive_2155_);
                        v_a_2152_ = v___x_2163_;
                        v_b_2153_ = v___x_2161_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2159_);
                        return v___x_2161_;
                    }
                } else {
                    leanh::lean_dec(v_a_2152_);
                    return v_b_2153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg___boxed(
    mut v_s_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
    mut v_b_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2169_: u32 = 0;
    let mut v_b_boxed_2170_: u8 = 0;
    let mut v_res_2171_: u8 = 0;
    let mut v_r_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2169_ = leanh::lean_unbox_uint32(v_a_2166_);
    leanh::lean_dec(v_a_2166_);
    v_b_boxed_2170_ = (leanh::lean_unbox(v_b_2168_) as u8);
    v_res_2171_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_2165_, v_a_boxed_2169_, v_a_2167_, v_b_boxed_2170_);
    leanh::lean_dec_ref(v_s_2165_);
    v_r_2172_ = leanh::lean_box((v_res_2171_) as usize);
    return v_r_2172_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(
    mut v_a_2173_: u32,
    mut v_s_2174_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_searcher_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: u8 = 0;
    v_searcher_2175_ = leanh::lean_unsigned_to_nat(0);
    v___x_2176_ = 0;
    v___x_2177_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_2174_, v_a_2173_, v_searcher_2175_, v___x_2176_);
    return v___x_2177_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2___boxed(
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_s_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2180_: u32 = 0;
    let mut v_res_2181_: u8 = 0;
    let mut v_r_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2180_ = leanh::lean_unbox_uint32(v_a_2178_);
    leanh::lean_dec(v_a_2178_);
    v_res_2181_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v_a_boxed_2180_, v_s_2179_);
    leanh::lean_dec_ref(v_s_2179_);
    v_r_2182_ = leanh::lean_box((v_res_2181_) as usize);
    return v_r_2182_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(
    mut v_comp_2186_: *mut leanh::LeanObject,
    mut v_as_2187_: *mut leanh::LeanObject,
    mut v_sz_2188_: usize,
    mut v_i_2189_: usize,
    mut v_b_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: u32 = 0;
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: usize = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2191_ = lean_usize_dec_lt(v_i_2189_, v_sz_2188_);
                if v___x_2191_ == 0 {
                    leanh::lean_dec_ref(v_comp_2186_);
                    leanh::lean_inc_ref(v_b_2190_);
                    return v_b_2190_;
                } else {
                    v___x_2192_ = leanh::lean_box(0);
                    v_a_2193_ = lean_array_uget_borrowed(v_as_2187_, v_i_2189_);
                    v___x_2194_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2195_ = lean_string_utf8_byte_size(v_comp_2186_);
                    leanh::lean_inc_ref(v_comp_2186_);
                    v___x_2196_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2196_, 0, v_comp_2186_);
                    leanh::lean_ctor_set(v___x_2196_, 1, v___x_2194_);
                    leanh::lean_ctor_set(v___x_2196_, 2, v___x_2195_);
                    v___x_2197_ = leanh::lean_unbox_uint32(v_a_2193_);
                    v___x_2198_ = l_String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2(v___x_2197_, v___x_2196_);
                    leanh::lean_dec_ref_known(v___x_2196_, 3);
                    if v___x_2198_ == 0 {
                        v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0;
                        v___x_2200_ = 1usize;
                        v___x_2201_ = lean_usize_add(v_i_2189_, v___x_2200_);
                        v_i_2189_ = v___x_2201_;
                        v_b_2190_ = v___x_2199_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_comp_2186_);
                        leanh::lean_inc(v_a_2193_);
                        v___x_2203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2203_, 0, v_a_2193_);
                        v___x_2204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2204_, 0, v___x_2203_);
                        v___x_2205_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2205_, 0, v___x_2204_);
                        leanh::lean_ctor_set(v___x_2205_, 1, v___x_2192_);
                        return v___x_2205_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___boxed(
    mut v_comp_2206_: *mut leanh::LeanObject,
    mut v_as_2207_: *mut leanh::LeanObject,
    mut v_sz_2208_: *mut leanh::LeanObject,
    mut v_i_2209_: *mut leanh::LeanObject,
    mut v_b_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2211_: usize = 0;
    let mut v_i_boxed_2212_: usize = 0;
    let mut v_res_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2211_ = leanh::lean_unbox_usize(v_sz_2208_);
    leanh::lean_dec(v_sz_2208_);
    v_i_boxed_2212_ = leanh::lean_unbox_usize(v_i_2209_);
    leanh::lean_dec(v_i_2209_);
    v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_2206_, v_as_2207_, v_sz_boxed_2211_, v_i_boxed_2212_, v_b_2210_);
    leanh::lean_dec_ref(v_b_2210_);
    leanh::lean_dec_ref(v_as_2207_);
    return v_res_2213_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(
    mut v_a_2214_: *mut leanh::LeanObject,
    mut v_as_2215_: *mut leanh::LeanObject,
    mut v_i_2216_: usize,
    mut v_stop_2217_: usize,
) -> u8 {
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: usize = 0;
    let mut v___x_2222_: usize = 0;
    let mut v___x_2224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2218_ = lean_usize_dec_eq(v_i_2216_, v_stop_2217_);
                if v___x_2218_ == 0 {
                    v___x_2219_ = lean_array_uget_borrowed(v_as_2215_, v_i_2216_);
                    v___x_2220_ = lean_string_dec_eq(v_a_2214_, v___x_2219_);
                    if v___x_2220_ == 0 {
                        v___x_2221_ = 1usize;
                        v___x_2222_ = lean_usize_add(v_i_2216_, v___x_2221_);
                        v_i_2216_ = v___x_2222_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2220_;
                    }
                } else {
                    v___x_2224_ = 0;
                    return v___x_2224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1___boxed(
    mut v_a_2225_: *mut leanh::LeanObject,
    mut v_as_2226_: *mut leanh::LeanObject,
    mut v_i_2227_: *mut leanh::LeanObject,
    mut v_stop_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2229_: usize = 0;
    let mut v_stop_boxed_2230_: usize = 0;
    let mut v_res_2231_: u8 = 0;
    let mut v_r_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2229_ = leanh::lean_unbox_usize(v_i_2227_);
    leanh::lean_dec(v_i_2227_);
    v_stop_boxed_2230_ = leanh::lean_unbox_usize(v_stop_2228_);
    leanh::lean_dec(v_stop_2228_);
    v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_2225_, v_as_2226_, v_i_boxed_2229_, v_stop_boxed_2230_);
    leanh::lean_dec_ref(v_as_2226_);
    leanh::lean_dec_ref(v_a_2225_);
    v_r_2232_ = leanh::lean_box((v_res_2231_) as usize);
    return v_r_2232_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(
    mut v_as_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    v___x_2235_ = leanh::lean_unsigned_to_nat(0);
    v___x_2236_ = lean_array_get_size(v_as_2233_);
    v___x_2237_ = lean_nat_dec_lt(v___x_2235_, v___x_2236_);
    if v___x_2237_ == 0 {
        return v___x_2237_;
    } else {
        if v___x_2237_ == 0 {
            return v___x_2237_;
        } else {
            let mut v___x_2238_: usize = 0;
            let mut v___x_2239_: usize = 0;
            let mut v___x_2240_: u8 = 0;
            v___x_2238_ = 0usize;
            v___x_2239_ = lean_usize_of_nat(v___x_2236_);
            v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1_spec__1(v_a_2234_, v_as_2233_, v___x_2238_, v___x_2239_);
            return v___x_2240_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1___boxed(
    mut v_as_2241_: *mut leanh::LeanObject,
    mut v_a_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2243_: u8 = 0;
    let mut v_r_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2243_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v_as_2241_, v_a_2242_);
    leanh::lean_dec_ref(v_a_2242_);
    leanh::lean_dec_ref(v_as_2241_);
    v_r_2244_ = leanh::lean_box((v_res_2243_) as usize);
    return v_r_2244_;
}
pub unsafe fn _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0()
-> usize {
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2246_: usize = 0;
    v___x_2245_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
    v_sz_2246_ = lean_array_size(v___x_2245_);
    return v_sz_2246_;
}
pub unsafe fn l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(
    mut v_comp_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: u8 = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2259_: usize = 0;
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u32 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2252_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenNames;
                v___x_2253_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_comp_2251_);
                v___x_2254_ = l_String_mapAux___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__0(v_comp_2251_, v___x_2253_);
                v___x_2255_ = l_Array_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__1(v___x_2252_, v___x_2254_);
                leanh::lean_dec_ref(v___x_2254_);
                if v___x_2255_ == 0 {
                    v___x_2256_ = l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars;
                    v___x_2257_ = leanh::lean_box(0);
                    v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3___closed__0;
                    v_sz_2259_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0_once), _init_l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__0);
                    v___x_2260_ = 0usize;
                    v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__3(v_comp_2251_, v___x_2256_, v_sz_2259_, v___x_2260_, v___x_2258_);
                    v_fst_2262_ = leanh::lean_ctor_get(v___x_2261_, 0);
                    leanh::lean_inc(v_fst_2262_);
                    leanh::lean_dec_ref(v___x_2261_);
                    if leanh::lean_obj_tag(v_fst_2262_) == 0 {
                        return v___x_2257_;
                    } else {
                        v_val_2263_ = leanh::lean_ctor_get(v_fst_2262_, 0);
                        leanh::lean_inc(v_val_2263_);
                        leanh::lean_dec_ref_known(v_fst_2262_, 1);
                        if leanh::lean_obj_tag(v_val_2263_) == 1 {
                            v_val_2264_ = leanh::lean_ctor_get(v_val_2263_, 0);
                            v_isSharedCheck_2278_ =
                                (!leanh::lean_is_exclusive(v_val_2263_)) as u8;
                            if v_isSharedCheck_2278_ == 0 {
                                v___x_2266_ = v_val_2263_;
                                v_isShared_2267_ = v_isSharedCheck_2278_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2264_);
                                leanh::lean_dec(v_val_2263_);
                                v___x_2266_ = leanh::lean_box(0);
                                v_isShared_2267_ = v_isSharedCheck_2278_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_2263_);
                            return v___x_2257_;
                        }
                    }
                } else {
                    v___x_2279_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__3;
                    v___x_2280_ = lean_string_append(v___x_2279_, v_comp_2251_);
                    leanh::lean_dec_ref(v_comp_2251_);
                    v___x_2281_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__4;
                    v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
                    v___x_2283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2283_, 0, v___x_2282_);
                    return v___x_2283_;
                }
            }
            1 => {
                v___x_2268_ =
                    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__1;
                v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0;
                v___x_2270_ = leanh::lean_unbox_uint32(v_val_2264_);
                leanh::lean_dec(v_val_2264_);
                v___x_2271_ = lean_string_push(v___x_2269_, v___x_2270_);
                v___x_2272_ = lean_string_append(v___x_2268_, v___x_2271_);
                leanh::lean_dec_ref(v___x_2271_);
                v___x_2273_ =
                    l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability___closed__2;
                v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2274_);
                    v___x_2276_ = v___x_2266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(
    mut v_s_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: u32,
    mut v_inst_2286_: *mut leanh::LeanObject,
    mut v_R_2287_: *mut leanh::LeanObject,
    mut v_a_2288_: *mut leanh::LeanObject,
    mut v_b_2289_: u8,
    mut v_c_2290_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2291_: u8 = 0;
    v___x_2291_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___redArg(v_s_2284_, v_a_2285_, v_a_2288_, v_b_2289_);
    return v___x_2291_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3___boxed(
    mut v_s_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_inst_2294_: *mut leanh::LeanObject,
    mut v_R_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
    mut v_b_2297_: *mut leanh::LeanObject,
    mut v_c_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2299_: u32 = 0;
    let mut v_b_boxed_2300_: u8 = 0;
    let mut v_res_2301_: u8 = 0;
    let mut v_r_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2299_ = leanh::lean_unbox_uint32(v_a_2293_);
    leanh::lean_dec(v_a_2293_);
    v_b_boxed_2300_ = (leanh::lean_unbox(v_b_2297_) as u8);
    v_res_2301_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability_spec__2_spec__3(v_s_2292_, v_a_boxed_2299_, v_inst_2294_, v_R_2295_, v_a_2296_, v_b_boxed_2300_, v_c_2298_);
    leanh::lean_dec_ref(v_s_2292_);
    v_r_2302_ = leanh::lean_box((v_res_2301_) as usize);
    return v_r_2302_;
}
pub unsafe fn l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(
    mut v_mainModule_2305_: *mut leanh::LeanObject,
    mut v_inputCtx_2306_: *mut leanh::LeanObject,
    mut v_startPos_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
    mut v_a_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v_fileName_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v_pre_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_2308_) {
                0 => {
                    leanh::lean_dec_ref(v_inputCtx_2306_);
                    leanh::lean_dec(v_mainModule_2305_);
                    return v_a_2309_;
                }
                1 => {
                    v_pre_2310_ = leanh::lean_ctor_get(v_a_2308_, 0);
                    leanh::lean_inc(v_pre_2310_);
                    v_str_2311_ = leanh::lean_ctor_get(v_a_2308_, 1);
                    leanh::lean_inc_ref(v_str_2311_);
                    leanh::lean_dec_ref_known(v_a_2308_, 2);
                    v___x_2312_ =
                        l___private_Lean_Elab_Import_0__Lean_Elab_checkComponentPortability(
                            v_str_2311_,
                        );
                    if leanh::lean_obj_tag(v___x_2312_) == 0 {
                        v_a_2308_ = v_pre_2310_;
                        state = 0;
                        continue;
                    } else {
                        v_val_2314_ = leanh::lean_ctor_get(v___x_2312_, 0);
                        v_isSharedCheck_2339_ =
                            (!leanh::lean_is_exclusive(v___x_2312_)) as u8;
                        if v_isSharedCheck_2339_ == 0 {
                            v___x_2316_ = v___x_2312_;
                            v_isShared_2317_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2314_);
                            leanh::lean_dec(v___x_2312_);
                            v___x_2316_ = leanh::lean_box(0);
                            v_isShared_2317_ = v_isSharedCheck_2339_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_pre_2340_ = leanh::lean_ctor_get(v_a_2308_, 0);
                    leanh::lean_inc(v_pre_2340_);
                    leanh::lean_dec_ref_known(v_a_2308_, 2);
                    v_a_2308_ = v_pre_2340_;
                    state = 0;
                    continue;
                }
            },
            1 => {
                v_fileName_2318_ = leanh::lean_ctor_get(v_inputCtx_2306_, 1);
                v_fileMap_2319_ = leanh::lean_ctor_get(v_inputCtx_2306_, 2);
                leanh::lean_inc_ref(v_fileMap_2319_);
                v___x_2320_ = l_Lean_FileMap_toPosition(v_fileMap_2319_, v_startPos_2307_);
                v___x_2321_ = leanh::lean_box(0);
                v___x_2322_ = 0;
                v___x_2323_ = 2;
                v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0;
                v___x_2325_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__0;
                v___x_2326_ = 1;
                leanh::lean_inc(v_mainModule_2305_);
                v___x_2327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_mainModule_2305_,
                    v___x_2326_,
                );
                v___x_2328_ = lean_string_append(v___x_2325_, v___x_2327_);
                leanh::lean_dec_ref(v___x_2327_);
                v___x_2329_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___closed__1;
                v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
                v___x_2331_ = lean_string_append(v___x_2330_, v_val_2314_);
                leanh::lean_dec(v_val_2314_);
                if v_isShared_2317_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2316_, 3);
                    leanh::lean_ctor_set(v___x_2316_, 0, v___x_2331_);
                    v___x_2333_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2331_);
                    v___x_2333_ = v_reuseFailAlloc_2338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2334_ = l_Lean_MessageData_ofFormat(v___x_2333_);
                leanh::lean_inc_ref(v_fileName_2318_);
                v___x_2335_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2335_, 0, v_fileName_2318_);
                leanh::lean_ctor_set(v___x_2335_, 1, v___x_2320_);
                leanh::lean_ctor_set(v___x_2335_, 2, v___x_2321_);
                leanh::lean_ctor_set(v___x_2335_, 3, v___x_2324_);
                leanh::lean_ctor_set(v___x_2335_, 4, v___x_2334_);
                leanh::lean_ctor_set_uint8(
                    v___x_2335_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2322_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2335_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2323_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2335_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_2322_,
                );
                v___x_2336_ = l_Lean_MessageLog_add(v___x_2335_, v_a_2309_);
                v_a_2308_ = v_pre_2310_;
                v_a_2309_ = v___x_2336_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go___boxed(
    mut v_mainModule_2342_: *mut leanh::LeanObject,
    mut v_inputCtx_2343_: *mut leanh::LeanObject,
    mut v_startPos_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2347_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(
        v_mainModule_2342_,
        v_inputCtx_2343_,
        v_startPos_2344_,
        v_a_2345_,
        v_a_2346_,
    );
    leanh::lean_dec(v_startPos_2344_);
    return v_res_2347_;
}
pub unsafe fn l_Lean_Elab_checkModuleNamePortability(
    mut v_mainModule_2348_: *mut leanh::LeanObject,
    mut v_inputCtx_2349_: *mut leanh::LeanObject,
    mut v_startPos_2350_: *mut leanh::LeanObject,
    mut v_messages_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mainModule_2348_);
    v___x_2352_ = l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(
        v_mainModule_2348_,
        v_inputCtx_2349_,
        v_startPos_2350_,
        v_mainModule_2348_,
        v_messages_2351_,
    );
    return v___x_2352_;
}
pub unsafe fn l_Lean_Elab_checkModuleNamePortability___boxed(
    mut v_mainModule_2353_: *mut leanh::LeanObject,
    mut v_inputCtx_2354_: *mut leanh::LeanObject,
    mut v_startPos_2355_: *mut leanh::LeanObject,
    mut v_messages_2356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_Elab_checkModuleNamePortability(
        v_mainModule_2353_,
        v_inputCtx_2354_,
        v_startPos_2355_,
        v_messages_2356_,
    );
    leanh::lean_dec(v_startPos_2355_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_Elab_processHeaderCore(
    mut v_startPos_2358_: *mut leanh::LeanObject,
    mut v_imports_2359_: *mut leanh::LeanObject,
    mut v_isModule_2360_: u8,
    mut v_opts_2361_: *mut leanh::LeanObject,
    mut v_messages_2362_: *mut leanh::LeanObject,
    mut v_inputCtx_2363_: *mut leanh::LeanObject,
    mut v_trustLevel_2364_: u32,
    mut v_plugins_2365_: *mut leanh::LeanObject,
    mut v_leakEnv_2366_: u8,
    mut v_mainModule_2367_: *mut leanh::LeanObject,
    mut v_package_x3f_2368_: *mut leanh::LeanObject,
    mut v_arts_2369_: *mut leanh::LeanObject,
    mut v_headerStx_x3f_2370_: *mut leanh::LeanObject,
    mut v_origHeaderStx_x3f_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u8 = 0;
    let mut v___y_2385_: u8 = 0;
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2392_: u32 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v___x_2418_: u8 = 0;
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2383_ = 1;
                if v_isModule_2360_ == 0 {
                    v___x_2418_ = 2;
                    v___y_2385_ = v___x_2418_;
                    state = 2;
                    continue;
                } else {
                    v___x_2419_ = l_Lean_Elab_inServer;
                    v___x_2420_ =
                        l_Lean_Option_get___at___00Lean_Elab_checkDeprecatedImports_spec__0(
                            v_opts_2361_,
                            v___x_2419_,
                        );
                    if v___x_2420_ == 0 {
                        v___x_2421_ = 0;
                        v___y_2385_ = v___x_2421_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2422_ = 1;
                        v___y_2385_ = v___x_2422_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_n(v_mainModule_2367_, 2);
                v___x_2376_ = l_Lean_Environment_setMainModule(v_fst_2374_, v_mainModule_2367_);
                v___x_2377_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
                v___x_2378_ = l_Lean_PersistentEnvExtension_setState___redArg(
                    v___x_2377_,
                    v___x_2376_,
                    v_package_x3f_2368_,
                );
                leanh::lean_inc_ref(v_inputCtx_2363_);
                v___x_2379_ = l_Lean_Elab_checkDeprecatedImports(
                    v___x_2378_,
                    v_imports_2359_,
                    v_opts_2361_,
                    v_inputCtx_2363_,
                    v_startPos_2358_,
                    v_snd_2375_,
                    v_headerStx_x3f_2370_,
                    v_origHeaderStx_x3f_2371_,
                );
                leanh::lean_dec_ref(v_imports_2359_);
                v___x_2380_ =
                    l___private_Lean_Elab_Import_0__Lean_Elab_checkModuleNamePortability_go(
                        v_mainModule_2367_,
                        v_inputCtx_2363_,
                        v_startPos_2358_,
                        v_mainModule_2367_,
                        v___x_2379_,
                    );
                v___x_2381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2381_, 0, v___x_2378_);
                leanh::lean_ctor_set(v___x_2381_, 1, v___x_2380_);
                v___x_2382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2382_, 0, v___x_2381_);
                return v___x_2382_;
            }
            2 => {
                leanh::lean_inc_ref(v_opts_2361_);
                leanh::lean_inc_ref(v_imports_2359_);
                v___x_2386_ = l_Lean_importModules(
                    v_imports_2359_,
                    v_opts_2361_,
                    v_trustLevel_2364_,
                    v_plugins_2365_,
                    v_leakEnv_2366_,
                    v___x_2383_,
                    v___y_2385_,
                    v_arts_2369_,
                );
                if leanh::lean_obj_tag(v___x_2386_) == 0 {
                    v_a_2387_ = leanh::lean_ctor_get(v___x_2386_, 0);
                    leanh::lean_inc(v_a_2387_);
                    leanh::lean_dec_ref_known(v___x_2386_, 1);
                    v_fst_2374_ = v_a_2387_;
                    v_snd_2375_ = v_messages_2362_;
                    state = 1;
                    continue;
                } else {
                    v_a_2388_ = leanh::lean_ctor_get(v___x_2386_, 0);
                    v_isSharedCheck_2417_ = (!leanh::lean_is_exclusive(v___x_2386_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2390_ = v___x_2386_;
                        v_isShared_2391_ = v_isSharedCheck_2417_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2388_);
                        leanh::lean_dec(v___x_2386_);
                        v___x_2390_ = leanh::lean_box(0);
                        v_isShared_2391_ = v_isSharedCheck_2417_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2392_ = 0;
                v___x_2393_ = lean_mk_empty_environment(v___x_2392_);
                if leanh::lean_obj_tag(v___x_2393_) == 0 {
                    v_a_2394_ = leanh::lean_ctor_get(v___x_2393_, 0);
                    leanh::lean_inc(v_a_2394_);
                    leanh::lean_dec_ref_known(v___x_2393_, 1);
                    v_fileName_2395_ = leanh::lean_ctor_get(v_inputCtx_2363_, 1);
                    v_fileMap_2396_ = leanh::lean_ctor_get(v_inputCtx_2363_, 2);
                    leanh::lean_inc_ref(v_fileMap_2396_);
                    v___x_2397_ = l_Lean_FileMap_toPosition(v_fileMap_2396_, v_startPos_2358_);
                    v___x_2398_ = leanh::lean_box(0);
                    v___x_2399_ = 0;
                    v___x_2400_ = 2;
                    v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_checkDeprecatedImports_spec__1___closed__0;
                    v___x_2402_ = lean_io_error_to_string(v_a_2388_);
                    if v_isShared_2391_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2390_, 3);
                        leanh::lean_ctor_set(v___x_2390_, 0, v___x_2402_);
                        v___x_2404_ = v___x_2390_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2408_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2402_);
                        v___x_2404_ = v_reuseFailAlloc_2408_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2390_);
                    leanh::lean_dec(v_a_2388_);
                    leanh::lean_dec(v_origHeaderStx_x3f_2371_);
                    leanh::lean_dec(v_headerStx_x3f_2370_);
                    leanh::lean_dec(v_package_x3f_2368_);
                    leanh::lean_dec(v_mainModule_2367_);
                    leanh::lean_dec_ref(v_inputCtx_2363_);
                    leanh::lean_dec_ref(v_messages_2362_);
                    leanh::lean_dec_ref(v_opts_2361_);
                    leanh::lean_dec_ref(v_imports_2359_);
                    v_a_2409_ = leanh::lean_ctor_get(v___x_2393_, 0);
                    v_isSharedCheck_2416_ = (!leanh::lean_is_exclusive(v___x_2393_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v___x_2411_ = v___x_2393_;
                        v_isShared_2412_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2409_);
                        leanh::lean_dec(v___x_2393_);
                        v___x_2411_ = leanh::lean_box(0);
                        v_isShared_2412_ = v_isSharedCheck_2416_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2405_ = l_Lean_MessageData_ofFormat(v___x_2404_);
                leanh::lean_inc_ref(v_fileName_2395_);
                v___x_2406_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2406_, 0, v_fileName_2395_);
                leanh::lean_ctor_set(v___x_2406_, 1, v___x_2397_);
                leanh::lean_ctor_set(v___x_2406_, 2, v___x_2398_);
                leanh::lean_ctor_set(v___x_2406_, 3, v___x_2401_);
                leanh::lean_ctor_set(v___x_2406_, 4, v___x_2405_);
                leanh::lean_ctor_set_uint8(
                    v___x_2406_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2399_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2406_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2400_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2406_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_2399_,
                );
                v___x_2407_ = l_Lean_MessageLog_add(v___x_2406_, v_messages_2362_);
                v_fst_2374_ = v_a_2394_;
                v_snd_2375_ = v___x_2407_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2412_ == 0 {
                    v___x_2414_ = v___x_2411_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2415_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
                    v___x_2414_ = v_reuseFailAlloc_2415_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_processHeaderCore___boxed(
    mut v_startPos_2423_: *mut leanh::LeanObject,
    mut v_imports_2424_: *mut leanh::LeanObject,
    mut v_isModule_2425_: *mut leanh::LeanObject,
    mut v_opts_2426_: *mut leanh::LeanObject,
    mut v_messages_2427_: *mut leanh::LeanObject,
    mut v_inputCtx_2428_: *mut leanh::LeanObject,
    mut v_trustLevel_2429_: *mut leanh::LeanObject,
    mut v_plugins_2430_: *mut leanh::LeanObject,
    mut v_leakEnv_2431_: *mut leanh::LeanObject,
    mut v_mainModule_2432_: *mut leanh::LeanObject,
    mut v_package_x3f_2433_: *mut leanh::LeanObject,
    mut v_arts_2434_: *mut leanh::LeanObject,
    mut v_headerStx_x3f_2435_: *mut leanh::LeanObject,
    mut v_origHeaderStx_x3f_2436_: *mut leanh::LeanObject,
    mut v_a_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isModule_boxed_2438_: u8 = 0;
    let mut v_trustLevel_boxed_2439_: u32 = 0;
    let mut v_leakEnv_boxed_2440_: u8 = 0;
    let mut v_res_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isModule_boxed_2438_ = (leanh::lean_unbox(v_isModule_2425_) as u8);
    v_trustLevel_boxed_2439_ = leanh::lean_unbox_uint32(v_trustLevel_2429_);
    leanh::lean_dec(v_trustLevel_2429_);
    v_leakEnv_boxed_2440_ = (leanh::lean_unbox(v_leakEnv_2431_) as u8);
    v_res_2441_ = l_Lean_Elab_processHeaderCore(
        v_startPos_2423_,
        v_imports_2424_,
        v_isModule_boxed_2438_,
        v_opts_2426_,
        v_messages_2427_,
        v_inputCtx_2428_,
        v_trustLevel_boxed_2439_,
        v_plugins_2430_,
        v_leakEnv_boxed_2440_,
        v_mainModule_2432_,
        v_package_x3f_2433_,
        v_arts_2434_,
        v_headerStx_x3f_2435_,
        v_origHeaderStx_x3f_2436_,
    );
    leanh::lean_dec(v_startPos_2423_);
    return v_res_2441_;
}
pub unsafe fn l_Lean_Elab_processHeader(
    mut v_header_2442_: *mut leanh::LeanObject,
    mut v_opts_2443_: *mut leanh::LeanObject,
    mut v_messages_2444_: *mut leanh::LeanObject,
    mut v_inputCtx_2445_: *mut leanh::LeanObject,
    mut v_trustLevel_2446_: u32,
    mut v_plugins_2447_: *mut leanh::LeanObject,
    mut v_leakEnv_2448_: u8,
    mut v_mainModule_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = l_Lean_Elab_HeaderSyntax_startPos(v_header_2442_);
    v___x_2452_ = 1;
    leanh::lean_inc(v_header_2442_);
    v___x_2453_ = l_Lean_Elab_HeaderSyntax_imports(v_header_2442_, v___x_2452_);
    v___x_2454_ = l_Lean_Elab_HeaderSyntax_isModule(v_header_2442_);
    v___x_2455_ = leanh::lean_box(0);
    v___x_2456_ = leanh::lean_box(1);
    v___x_2457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2457_, 0, v_header_2442_);
    v___x_2458_ = l_Lean_Elab_processHeaderCore(
        v___x_2451_,
        v___x_2453_,
        v___x_2454_,
        v_opts_2443_,
        v_messages_2444_,
        v_inputCtx_2445_,
        v_trustLevel_2446_,
        v_plugins_2447_,
        v_leakEnv_2448_,
        v_mainModule_2449_,
        v___x_2455_,
        v___x_2456_,
        v___x_2457_,
        v___x_2455_,
    );
    leanh::lean_dec(v___x_2451_);
    return v___x_2458_;
}
pub unsafe fn l_Lean_Elab_processHeader___boxed(
    mut v_header_2459_: *mut leanh::LeanObject,
    mut v_opts_2460_: *mut leanh::LeanObject,
    mut v_messages_2461_: *mut leanh::LeanObject,
    mut v_inputCtx_2462_: *mut leanh::LeanObject,
    mut v_trustLevel_2463_: *mut leanh::LeanObject,
    mut v_plugins_2464_: *mut leanh::LeanObject,
    mut v_leakEnv_2465_: *mut leanh::LeanObject,
    mut v_mainModule_2466_: *mut leanh::LeanObject,
    mut v_a_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trustLevel_boxed_2468_: u32 = 0;
    let mut v_leakEnv_boxed_2469_: u8 = 0;
    let mut v_res_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trustLevel_boxed_2468_ = leanh::lean_unbox_uint32(v_trustLevel_2463_);
    leanh::lean_dec(v_trustLevel_2463_);
    v_leakEnv_boxed_2469_ = (leanh::lean_unbox(v_leakEnv_2465_) as u8);
    v_res_2470_ = l_Lean_Elab_processHeader(
        v_header_2459_,
        v_opts_2460_,
        v_messages_2461_,
        v_inputCtx_2462_,
        v_trustLevel_boxed_2468_,
        v_plugins_2464_,
        v_leakEnv_boxed_2469_,
        v_mainModule_2466_,
    );
    return v_res_2470_;
}
pub unsafe fn l_Lean_Elab_parseImports(
    mut v_input_2472_: *mut leanh::LeanObject,
    mut v_fileName_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: u8 = 0;
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputCtx_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v_snd_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v_snd_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v_fileMap_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_unused_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2510_: u8 = 0;
    let mut v_unused_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut v_a_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_fileName_2473_) == 0 {
                    v___x_2521_ = l_Lean_Elab_parseImports___closed__0;
                    v___y_2476_ = v___x_2521_;
                    state = 1;
                    continue;
                } else {
                    v_val_2522_ = leanh::lean_ctor_get(v_fileName_2473_, 0);
                    leanh::lean_inc(v_val_2522_);
                    leanh::lean_dec_ref_known(v_fileName_2473_, 1);
                    v___y_2476_ = v_val_2522_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2477_ = 1;
                v___x_2478_ = lean_string_utf8_byte_size(v_input_2472_);
                v_inputCtx_2479_ = l_Lean_Parser_mkInputContext___redArg(
                    v_input_2472_,
                    v___y_2476_,
                    v___x_2477_,
                    v___x_2478_,
                );
                leanh::lean_inc_ref(v_inputCtx_2479_);
                v___x_2480_ = l_Lean_Parser_parseHeader(v_inputCtx_2479_);
                if leanh::lean_obj_tag(v___x_2480_) == 0 {
                    v_a_2481_ = leanh::lean_ctor_get(v___x_2480_, 0);
                    v_isSharedCheck_2512_ = (!leanh::lean_is_exclusive(v___x_2480_)) as u8;
                    if v_isSharedCheck_2512_ == 0 {
                        v___x_2483_ = v___x_2480_;
                        v_isShared_2484_ = v_isSharedCheck_2512_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2481_);
                        leanh::lean_dec(v___x_2480_);
                        v___x_2483_ = leanh::lean_box(0);
                        v_isShared_2484_ = v_isSharedCheck_2512_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inputCtx_2479_);
                    v_a_2513_ = leanh::lean_ctor_get(v___x_2480_, 0);
                    v_isSharedCheck_2520_ = (!leanh::lean_is_exclusive(v___x_2480_)) as u8;
                    if v_isSharedCheck_2520_ == 0 {
                        v___x_2515_ = v___x_2480_;
                        v_isShared_2516_ = v_isSharedCheck_2520_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2513_);
                        leanh::lean_dec(v___x_2480_);
                        v___x_2515_ = leanh::lean_box(0);
                        v_isShared_2516_ = v_isSharedCheck_2520_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2485_ = leanh::lean_ctor_get(v_a_2481_, 1);
                leanh::lean_inc(v_snd_2485_);
                v_fst_2486_ = leanh::lean_ctor_get(v_snd_2485_, 0);
                leanh::lean_inc(v_fst_2486_);
                v_fst_2487_ = leanh::lean_ctor_get(v_a_2481_, 0);
                v_isSharedCheck_2510_ = (!leanh::lean_is_exclusive(v_a_2481_)) as u8;
                if v_isSharedCheck_2510_ == 0 {
                    v_unused_2511_ = leanh::lean_ctor_get(v_a_2481_, 1);
                    leanh::lean_dec(v_unused_2511_);
                    v___x_2489_ = v_a_2481_;
                    v_isShared_2490_ = v_isSharedCheck_2510_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2487_);
                    leanh::lean_dec(v_a_2481_);
                    v___x_2489_ = leanh::lean_box(0);
                    v_isShared_2490_ = v_isSharedCheck_2510_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_snd_2491_ = leanh::lean_ctor_get(v_snd_2485_, 1);
                v_isSharedCheck_2508_ = (!leanh::lean_is_exclusive(v_snd_2485_)) as u8;
                if v_isSharedCheck_2508_ == 0 {
                    v_unused_2509_ = leanh::lean_ctor_get(v_snd_2485_, 0);
                    leanh::lean_dec(v_unused_2509_);
                    v___x_2493_ = v_snd_2485_;
                    v_isShared_2494_ = v_isSharedCheck_2508_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2491_);
                    leanh::lean_dec(v_snd_2485_);
                    v___x_2493_ = leanh::lean_box(0);
                    v_isShared_2494_ = v_isSharedCheck_2508_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fileMap_2495_ = leanh::lean_ctor_get(v_inputCtx_2479_, 2);
                leanh::lean_inc_ref(v_fileMap_2495_);
                leanh::lean_dec_ref(v_inputCtx_2479_);
                v_pos_2496_ = leanh::lean_ctor_get(v_fst_2486_, 0);
                leanh::lean_inc(v_pos_2496_);
                leanh::lean_dec(v_fst_2486_);
                v___x_2497_ = l_Lean_Elab_HeaderSyntax_imports(v_fst_2487_, v___x_2477_);
                v___x_2498_ = l_Lean_FileMap_toPosition(v_fileMap_2495_, v_pos_2496_);
                leanh::lean_dec(v_pos_2496_);
                if v_isShared_2494_ == 0 {
                    leanh::lean_ctor_set(v___x_2493_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2493_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_snd_2491_);
                    v___x_2500_ = v_reuseFailAlloc_2507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2490_ == 0 {
                    leanh::lean_ctor_set(v___x_2489_, 1, v___x_2500_);
                    leanh::lean_ctor_set(v___x_2489_, 0, v___x_2497_);
                    v___x_2502_ = v___x_2489_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2500_);
                    v___x_2502_ = v_reuseFailAlloc_2506_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2484_ == 0 {
                    leanh::lean_ctor_set(v___x_2483_, 0, v___x_2502_);
                    v___x_2504_ = v___x_2483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
                    v___x_2504_ = v_reuseFailAlloc_2505_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2504_;
            }
            8 => {
                if v_isShared_2516_ == 0 {
                    v___x_2518_ = v___x_2515_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
                    v___x_2518_ = v_reuseFailAlloc_2519_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_parseImports___boxed(
    mut v_input_2523_: *mut leanh::LeanObject,
    mut v_fileName_2524_: *mut leanh::LeanObject,
    mut v_a_2525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2526_ = l_Lean_Elab_parseImports(v_input_2523_, v_fileName_2524_);
    return v_res_2526_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(
    mut v_s_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2529_ = lean_get_stdout();
    v_putStr_2530_ = leanh::lean_ctor_get(v___x_2529_, 4);
    leanh::lean_inc_ref(v_putStr_2530_);
    leanh::lean_dec_ref(v___x_2529_);
    v___x_2531_ = leanh::lean_apply_2(v_putStr_2530_, v_s_2527_, leanh::lean_box(0));
    return v___x_2531_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0___boxed(
    mut v_s_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ =
        l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v_s_2532_);
    return v_res_2534_;
}
pub unsafe fn l_IO_println___at___00Lean_Elab_printImports_spec__0(
    mut v_s_2535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2537_: u32 = 0;
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = 10;
    v___x_2538_ = lean_string_push(v_s_2535_, v___x_2537_);
    v___x_2539_ =
        l_IO_print___at___00IO_println___at___00Lean_Elab_printImports_spec__0_spec__0(v___x_2538_);
    return v___x_2539_;
}
pub unsafe fn l_IO_println___at___00Lean_Elab_printImports_spec__0___boxed(
    mut v_s_2540_: *mut leanh::LeanObject,
    mut v_a_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2542_ = l_IO_println___at___00Lean_Elab_printImports_spec__0(v_s_2540_);
    return v_res_2542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(
    mut v_as_2543_: *mut leanh::LeanObject,
    mut v_sz_2544_: usize,
    mut v_i_2545_: usize,
    mut v_b_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: usize = 0;
    let mut v_a_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2548_ = lean_usize_dec_lt(v_i_2545_, v_sz_2544_);
                if v___x_2548_ == 0 {
                    v___x_2549_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2549_, 0, v_b_2546_);
                    return v___x_2549_;
                } else {
                    v_a_2550_ = lean_array_uget_borrowed(v_as_2543_, v_i_2545_);
                    v_module_2551_ = leanh::lean_ctor_get(v_a_2550_, 0);
                    leanh::lean_inc(v_module_2551_);
                    v___x_2552_ = l_Lean_findOLean(v_module_2551_);
                    if leanh::lean_obj_tag(v___x_2552_) == 0 {
                        v_a_2553_ = leanh::lean_ctor_get(v___x_2552_, 0);
                        leanh::lean_inc(v_a_2553_);
                        leanh::lean_dec_ref_known(v___x_2552_, 1);
                        v___x_2554_ =
                            l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_2553_);
                        if leanh::lean_obj_tag(v___x_2554_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2554_, 1);
                            v___x_2555_ = leanh::lean_box(0);
                            v___x_2556_ = 1usize;
                            v___x_2557_ = lean_usize_add(v_i_2545_, v___x_2556_);
                            v_i_2545_ = v___x_2557_;
                            v_b_2546_ = v___x_2555_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2554_;
                        }
                    } else {
                        v_a_2559_ = leanh::lean_ctor_get(v___x_2552_, 0);
                        v_isSharedCheck_2566_ =
                            (!leanh::lean_is_exclusive(v___x_2552_)) as u8;
                        if v_isSharedCheck_2566_ == 0 {
                            v___x_2561_ = v___x_2552_;
                            v_isShared_2562_ = v_isSharedCheck_2566_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2559_);
                            leanh::lean_dec(v___x_2552_);
                            v___x_2561_ = leanh::lean_box(0);
                            v_isShared_2562_ = v_isSharedCheck_2566_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1___boxed(
    mut v_as_2567_: *mut leanh::LeanObject,
    mut v_sz_2568_: *mut leanh::LeanObject,
    mut v_i_2569_: *mut leanh::LeanObject,
    mut v_b_2570_: *mut leanh::LeanObject,
    mut v___y_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2572_: usize = 0;
    let mut v_i_boxed_2573_: usize = 0;
    let mut v_res_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2572_ = leanh::lean_unbox_usize(v_sz_2568_);
    leanh::lean_dec(v_sz_2568_);
    v_i_boxed_2573_ = leanh::lean_unbox_usize(v_i_2569_);
    leanh::lean_dec(v_i_2569_);
    v_res_2574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_as_2567_, v_sz_boxed_2572_, v_i_boxed_2573_, v_b_2570_);
    leanh::lean_dec_ref(v_as_2567_);
    return v_res_2574_;
}
pub unsafe fn l_Lean_Elab_printImports(
    mut v_input_2575_: *mut leanh::LeanObject,
    mut v_fileName_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_unused_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2578_ = l_Lean_Elab_parseImports(v_input_2575_, v_fileName_2576_);
                if leanh::lean_obj_tag(v___x_2578_) == 0 {
                    v_a_2579_ = leanh::lean_ctor_get(v___x_2578_, 0);
                    leanh::lean_inc(v_a_2579_);
                    leanh::lean_dec_ref_known(v___x_2578_, 1);
                    v_fst_2580_ = leanh::lean_ctor_get(v_a_2579_, 0);
                    leanh::lean_inc(v_fst_2580_);
                    leanh::lean_dec(v_a_2579_);
                    v___x_2581_ = leanh::lean_box(0);
                    v_sz_2582_ = lean_array_size(v_fst_2580_);
                    v___x_2583_ = 0usize;
                    v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImports_spec__1(v_fst_2580_, v_sz_2582_, v___x_2583_, v___x_2581_);
                    leanh::lean_dec(v_fst_2580_);
                    if leanh::lean_obj_tag(v___x_2584_) == 0 {
                        v_isSharedCheck_2591_ =
                            (!leanh::lean_is_exclusive(v___x_2584_)) as u8;
                        if v_isSharedCheck_2591_ == 0 {
                            v_unused_2592_ = leanh::lean_ctor_get(v___x_2584_, 0);
                            leanh::lean_dec(v_unused_2592_);
                            v___x_2586_ = v___x_2584_;
                            v_isShared_2587_ = v_isSharedCheck_2591_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2584_);
                            v___x_2586_ = leanh::lean_box(0);
                            v_isShared_2587_ = v_isSharedCheck_2591_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2584_;
                    }
                } else {
                    v_a_2593_ = leanh::lean_ctor_get(v___x_2578_, 0);
                    v_isSharedCheck_2600_ = (!leanh::lean_is_exclusive(v___x_2578_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2595_ = v___x_2578_;
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2593_);
                        leanh::lean_dec(v___x_2578_);
                        v___x_2595_ = leanh::lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2587_ == 0 {
                    leanh::lean_ctor_set(v___x_2586_, 0, v___x_2581_);
                    v___x_2589_ = v___x_2586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2581_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2589_;
            }
            3 => {
                if v_isShared_2596_ == 0 {
                    v___x_2598_ = v___x_2595_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_printImports___boxed(
    mut v_input_2601_: *mut leanh::LeanObject,
    mut v_fileName_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Lean_Elab_printImports(v_input_2601_, v_fileName_2602_);
    return v_res_2604_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_as_2606_: *mut leanh::LeanObject,
    mut v_sz_2607_: usize,
    mut v_i_2608_: usize,
    mut v_b_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2611_: u8 = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: usize = 0;
    let mut v___x_2620_: usize = 0;
    let mut v_a_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2611_ = lean_usize_dec_lt(v_i_2608_, v_sz_2607_);
                if v___x_2611_ == 0 {
                    leanh::lean_dec(v_a_2605_);
                    v___x_2612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2612_, 0, v_b_2609_);
                    return v___x_2612_;
                } else {
                    v_a_2613_ = lean_array_uget_borrowed(v_as_2606_, v_i_2608_);
                    v_module_2614_ = leanh::lean_ctor_get(v_a_2613_, 0);
                    leanh::lean_inc(v_module_2614_);
                    leanh::lean_inc(v_a_2605_);
                    v___x_2615_ = l_Lean_findLean(v_a_2605_, v_module_2614_);
                    if leanh::lean_obj_tag(v___x_2615_) == 0 {
                        v_a_2616_ = leanh::lean_ctor_get(v___x_2615_, 0);
                        leanh::lean_inc(v_a_2616_);
                        leanh::lean_dec_ref_known(v___x_2615_, 1);
                        v___x_2617_ =
                            l_IO_println___at___00Lean_Elab_printImports_spec__0(v_a_2616_);
                        if leanh::lean_obj_tag(v___x_2617_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2617_, 1);
                            v___x_2618_ = leanh::lean_box(0);
                            v___x_2619_ = 1usize;
                            v___x_2620_ = lean_usize_add(v_i_2608_, v___x_2619_);
                            v_i_2608_ = v___x_2620_;
                            v_b_2609_ = v___x_2618_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2605_);
                            return v___x_2617_;
                        }
                    } else {
                        leanh::lean_dec(v_a_2605_);
                        v_a_2622_ = leanh::lean_ctor_get(v___x_2615_, 0);
                        v_isSharedCheck_2629_ =
                            (!leanh::lean_is_exclusive(v___x_2615_)) as u8;
                        if v_isSharedCheck_2629_ == 0 {
                            v___x_2624_ = v___x_2615_;
                            v_isShared_2625_ = v_isSharedCheck_2629_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2622_);
                            leanh::lean_dec(v___x_2615_);
                            v___x_2624_ = leanh::lean_box(0);
                            v_isShared_2625_ = v_isSharedCheck_2629_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2625_ == 0 {
                    v___x_2627_ = v___x_2624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
                    v___x_2627_ = v_reuseFailAlloc_2628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0___boxed(
    mut v_a_2630_: *mut leanh::LeanObject,
    mut v_as_2631_: *mut leanh::LeanObject,
    mut v_sz_2632_: *mut leanh::LeanObject,
    mut v_i_2633_: *mut leanh::LeanObject,
    mut v_b_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2636_: usize = 0;
    let mut v_i_boxed_2637_: usize = 0;
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2636_ = leanh::lean_unbox_usize(v_sz_2632_);
    leanh::lean_dec(v_sz_2632_);
    v_i_boxed_2637_ = leanh::lean_unbox_usize(v_i_2633_);
    leanh::lean_dec(v_i_2633_);
    v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_2630_, v_as_2631_, v_sz_boxed_2636_, v_i_boxed_2637_, v_b_2634_);
    leanh::lean_dec_ref(v_as_2631_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_Elab_printImportSrcs(
    mut v_input_2639_: *mut leanh::LeanObject,
    mut v_fileName_2640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2648_: usize = 0;
    let mut v___x_2649_: usize = 0;
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2657_: u8 = 0;
    let mut v_unused_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2666_: u8 = 0;
    let mut v_a_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2670_: u8 = 0;
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2642_ = l_Lean_getSrcSearchPath();
                if leanh::lean_obj_tag(v___x_2642_) == 0 {
                    v_a_2643_ = leanh::lean_ctor_get(v___x_2642_, 0);
                    leanh::lean_inc(v_a_2643_);
                    leanh::lean_dec_ref_known(v___x_2642_, 1);
                    v___x_2644_ = l_Lean_Elab_parseImports(v_input_2639_, v_fileName_2640_);
                    if leanh::lean_obj_tag(v___x_2644_) == 0 {
                        v_a_2645_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        leanh::lean_inc(v_a_2645_);
                        leanh::lean_dec_ref_known(v___x_2644_, 1);
                        v_fst_2646_ = leanh::lean_ctor_get(v_a_2645_, 0);
                        leanh::lean_inc(v_fst_2646_);
                        leanh::lean_dec(v_a_2645_);
                        v___x_2647_ = leanh::lean_box(0);
                        v_sz_2648_ = lean_array_size(v_fst_2646_);
                        v___x_2649_ = 0usize;
                        v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_printImportSrcs_spec__0(v_a_2643_, v_fst_2646_, v_sz_2648_, v___x_2649_, v___x_2647_);
                        leanh::lean_dec(v_fst_2646_);
                        if leanh::lean_obj_tag(v___x_2650_) == 0 {
                            v_isSharedCheck_2657_ =
                                (!leanh::lean_is_exclusive(v___x_2650_)) as u8;
                            if v_isSharedCheck_2657_ == 0 {
                                v_unused_2658_ = leanh::lean_ctor_get(v___x_2650_, 0);
                                leanh::lean_dec(v_unused_2658_);
                                v___x_2652_ = v___x_2650_;
                                v_isShared_2653_ = v_isSharedCheck_2657_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2650_);
                                v___x_2652_ = leanh::lean_box(0);
                                v_isShared_2653_ = v_isSharedCheck_2657_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_2650_;
                        }
                    } else {
                        leanh::lean_dec(v_a_2643_);
                        v_a_2659_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2666_ =
                            (!leanh::lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2666_ == 0 {
                            v___x_2661_ = v___x_2644_;
                            v_isShared_2662_ = v_isSharedCheck_2666_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2659_);
                            leanh::lean_dec(v___x_2644_);
                            v___x_2661_ = leanh::lean_box(0);
                            v_isShared_2662_ = v_isSharedCheck_2666_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fileName_2640_);
                    leanh::lean_dec_ref(v_input_2639_);
                    v_a_2667_ = leanh::lean_ctor_get(v___x_2642_, 0);
                    v_isSharedCheck_2674_ = (!leanh::lean_is_exclusive(v___x_2642_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v___x_2669_ = v___x_2642_;
                        v_isShared_2670_ = v_isSharedCheck_2674_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2667_);
                        leanh::lean_dec(v___x_2642_);
                        v___x_2669_ = leanh::lean_box(0);
                        v_isShared_2670_ = v_isSharedCheck_2674_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2653_ == 0 {
                    leanh::lean_ctor_set(v___x_2652_, 0, v___x_2647_);
                    v___x_2655_ = v___x_2652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2647_);
                    v___x_2655_ = v_reuseFailAlloc_2656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2655_;
            }
            3 => {
                if v_isShared_2662_ == 0 {
                    v___x_2664_ = v___x_2661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
                    v___x_2664_ = v_reuseFailAlloc_2665_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2664_;
            }
            5 => {
                if v_isShared_2670_ == 0 {
                    v___x_2672_ = v___x_2669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
                    v___x_2672_ = v_reuseFailAlloc_2673_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_printImportSrcs___boxed(
    mut v_input_2675_: *mut leanh::LeanObject,
    mut v_fileName_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Lean_Elab_printImportSrcs(v_input_2675_, v_fileName_2676_);
    return v_res_2678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Import(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeprecatedModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__1,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__2,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__3,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__4,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__5,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__6,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7 = _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars___closed__0___boxed__const__7,
    );
    l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars =
        _init_l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars();
    leanh::lean_mark_persistent(l___private_Lean_Elab_Import_0__Lean_Elab_osForbiddenChars);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Import(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Import(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DeprecatedModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Import(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Import(builtin);
}