// Lean compiler output
// Module: Lean.Linter.Builtin
// Imports: Lean.Linter.Util Lean.Elab.Command
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [115, 117, 115, 112, 105, 99, 105, 111, 117, 115, 85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 80, 97, 116, 116, 101, 114, 110, 115, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,1190709675906190208 as *mut LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 115, 117, 115, 112, 105, 99, 105, 111, 117, 115, 32, 117, 110, 101, 120, 112, 97, 110, 100, 101, 114, 32, 112, 97, 116, 116, 101, 114, 110, 115, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,3916942831794082747 as *mut LeanObject] };
static mut l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__2_value) as *mut LeanObject,7499624980761693169 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__4_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value: LeanStringObject<142> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 142, m_capacity: 142, m_length: 141, m_data: [85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 115, 32, 115, 104, 111, 117, 108, 100, 32, 109, 97, 116, 99, 104, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 97, 103, 97, 105, 110, 115, 116, 32, 97, 110, 32, 97, 110, 116, 105, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 96, 36, 95, 96, 32, 115, 111, 32, 97, 115, 32, 116, 111, 32, 98, 101, 32, 105, 110, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 111, 102, 32, 116, 104, 101, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 32, 111, 102, 32, 116, 104, 101, 32, 110, 97, 109, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [113, 117, 111, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__3_value) as *mut LeanObject,5855146430765573009 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__5_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__7_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__0_value) as *mut LeanObject,16529391333736644786 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__0_value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__1_value) as *mut LeanObject,3878072352281346923 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 112, 112, 95, 117, 110, 101, 120, 112, 97, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__3_value) as *mut LeanObject,1464131427232734893 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__1_value)
            as *mut LeanObject,
        8497769072906204829 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__3_value)
            as *mut LeanObject,
        14557702332550915328 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__5_value)
            as *mut LeanObject,
        9789339221525904376 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__7_value)
            as *mut LeanObject,
        5473625859156281626 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__10_value)
            as *mut LeanObject,
        2637955643238073017 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__14_value)
            as *mut LeanObject,
        7625897890118033792 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__15_value)
            as *mut LeanObject,
        8715860392475343861 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__17_value)
            as *mut LeanObject,
        2533412339571800130 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__20_value)
            as *mut LeanObject,
        9063780239635860524 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value)
        as *mut LeanObject;
static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__value) as *mut LeanObject,5496964320310671834 as *mut LeanObject] };
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_suspiciousUnexpanderPatterns: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_suspiciousUnexpanderPatterns___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(
    mut v_name_920_: *mut LeanObject,
    mut v_decl_921_: *mut LeanObject,
    mut v_ref_922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut v_unused_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_924_ = lean_ctor_get(v_decl_921_, 0);
                v_descr_925_ = lean_ctor_get(v_decl_921_, 1);
                v_deprecation_x3f_926_ = lean_ctor_get(v_decl_921_, 2);
                v___x_927_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_928_ = (lean_unbox(v_defValue_924_) as u8);
                lean_ctor_set_uint8(v___x_927_, 0 as u32, v___x_928_);
                lean_inc(v_deprecation_x3f_926_);
                lean_inc_ref(v_descr_925_);
                lean_inc_n(v_name_920_, 2);
                v___x_929_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_929_, 0, v_name_920_);
                lean_ctor_set(v___x_929_, 1, v_ref_922_);
                lean_ctor_set(v___x_929_, 2, v___x_927_);
                lean_ctor_set(v___x_929_, 3, v_descr_925_);
                lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_926_);
                v___x_930_ = lean_register_option(v_name_920_, v___x_929_);
                if lean_obj_tag(v___x_930_) == 0 {
                    v_isSharedCheck_938_ = (!lean_is_exclusive(v___x_930_)) as u8;
                    if v_isSharedCheck_938_ == 0 {
                        v_unused_939_ = lean_ctor_get(v___x_930_, 0);
                        lean_dec(v_unused_939_);
                        v___x_932_ = v___x_930_;
                        v_isShared_933_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_930_);
                        v___x_932_ = lean_box(0);
                        v_isShared_933_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_920_);
                    v_a_940_ = lean_ctor_get(v___x_930_, 0);
                    v_isSharedCheck_947_ = (!lean_is_exclusive(v___x_930_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_942_ = v___x_930_;
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_940_);
                        lean_dec(v___x_930_);
                        v___x_942_ = lean_box(0);
                        v_isShared_943_ = v_isSharedCheck_947_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_924_);
                v___x_934_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_934_, 0, v_name_920_);
                lean_ctor_set(v___x_934_, 1, v_defValue_924_);
                if v_isShared_933_ == 0 {
                    lean_ctor_set(v___x_932_, 0, v___x_934_);
                    v___x_936_ = v___x_932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
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
                    v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
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
    mut v_name_948_: *mut LeanObject,
    mut v_decl_949_: *mut LeanObject,
    mut v_ref_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
    lean_dec_ref(v_decl_949_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    v___x_972_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_973_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_974_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
    v___x_975_ = l_Lean_Option_register___at___00__private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4__spec__0(v___x_972_, v___x_973_, v___x_974_);
    return v___x_975_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4____boxed(
    mut v_a_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_977_: *mut LeanObject = core::ptr::null_mut();
    v_res_977_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
    return v_res_977_;
}
pub unsafe fn l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(
    mut v_o_978_: *mut LeanObject,
) -> u8 {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    v___x_979_ = l_Lean_Linter_linter_suspiciousUnexpanderPatterns;
    v___x_980_ = l_Lean_Linter_getLinterValue(v___x_979_, v_o_978_);
    return v___x_980_;
}
pub unsafe fn l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns___boxed(
    mut v_o_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_o_981_);
    lean_dec_ref(v_o_981_);
    v_r_983_ = lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(
    mut v_o_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_987_ = lean_st_ref_get(v___y_985_);
    v_env_988_ = lean_ctor_get(v___x_987_, 0);
    lean_inc_ref(v_env_988_);
    lean_dec(v___x_987_);
    v___x_989_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_990_ = lean_ctor_get(v___x_989_, 0);
    v_asyncMode_991_ = lean_ctor_get(v_toEnvExtension_990_, 2);
    v___x_992_ = lean_box(1);
    v___x_993_ = lean_box(0);
    v_linterSets_994_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_992_,
        v___x_989_,
        v_env_988_,
        v_asyncMode_991_,
        v___x_993_,
    );
    v___x_995_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_995_, 0, v_o_984_);
    lean_ctor_set(v___x_995_, 1, v_linterSets_994_);
    v___x_996_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_996_, 0, v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg___boxed(
    mut v_o_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1000_: *mut LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_997_, v___y_998_);
    lean_dec(v___y_998_);
    return v_res_1000_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_st_ref_get(v___y_1002_);
    v_scopes_1005_ = lean_ctor_get(v___x_1004_, 2);
    lean_inc(v_scopes_1005_);
    lean_dec(v___x_1004_);
    v___x_1006_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1007_ = l_List_head_x21___redArg(v___x_1006_, v_scopes_1005_);
    lean_dec(v_scopes_1005_);
    v_opts_1008_ = lean_ctor_get(v___x_1007_, 1);
    lean_inc_ref(v_opts_1008_);
    lean_dec(v___x_1007_);
    v___x_1009_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_opts_1008_, v___y_1002_);
    return v___x_1009_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0___boxed(
    mut v___y_1010_: *mut LeanObject,
    mut v___y_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(
            v___y_1010_,
            v___y_1011_,
        );
    lean_dec(v___y_1011_);
    lean_dec_ref(v___y_1010_);
    return v_res_1013_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(
    mut v_sz_1028_: usize,
    mut v_i_1029_: usize,
    mut v_bs_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1031_ = lean_usize_dec_lt(v_i_1029_, v_sz_1028_);
                if v___x_1031_ == 0 {
                    v___x_1032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1032_, 0, v_bs_1030_);
                    return v___x_1032_;
                } else {
                    v_v_1033_ = lean_array_uget(v_bs_1030_, v_i_1029_);
                    v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__3;
                    lean_inc(v_v_1033_);
                    v___x_1035_ = l_Lean_Syntax_isOfKind(v_v_1033_, v___x_1034_);
                    if v___x_1035_ == 0 {
                        lean_dec(v_v_1033_);
                        lean_dec_ref(v_bs_1030_);
                        v___x_1036_ = lean_box(0);
                        return v___x_1036_;
                    } else {
                        v___x_1037_ = lean_unsigned_to_nat(0);
                        v___x_1038_ = l_Lean_Syntax_getArg(v_v_1033_, v___x_1037_);
                        v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__5;
                        lean_inc(v___x_1038_);
                        v___x_1040_ = l_Lean_Syntax_isOfKind(v___x_1038_, v___x_1039_);
                        if v___x_1040_ == 0 {
                            lean_dec(v___x_1038_);
                            lean_dec(v_v_1033_);
                            lean_dec_ref(v_bs_1030_);
                            v___x_1041_ = lean_box(0);
                            return v___x_1041_;
                        } else {
                            v___x_1042_ = l_Lean_Syntax_getArg(v___x_1038_, v___x_1037_);
                            lean_dec(v___x_1038_);
                            v___x_1043_ = l_Lean_Syntax_matchesNull(v___x_1042_, v___x_1037_);
                            if v___x_1043_ == 0 {
                                lean_dec(v_v_1033_);
                                lean_dec_ref(v_bs_1030_);
                                v___x_1044_ = lean_box(0);
                                return v___x_1044_;
                            } else {
                                v___x_1045_ = lean_unsigned_to_nat(1);
                                v_bs_x27_1046_ =
                                    lean_array_uset(v_bs_1030_, v_i_1029_, v___x_1037_);
                                v___x_1047_ = l_Lean_Syntax_getArg(v_v_1033_, v___x_1045_);
                                lean_dec(v_v_1033_);
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
    mut v_sz_1052_: *mut LeanObject,
    mut v_i_1053_: *mut LeanObject,
    mut v_bs_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1055_: usize = 0;
    let mut v_i_boxed_1056_: usize = 0;
    let mut v_res_1057_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
    lean_dec(v_sz_1052_);
    v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
    lean_dec(v_i_1053_);
    v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(
    mut v_opts_1058_: *mut LeanObject,
    mut v_opt_1059_: *mut LeanObject,
) -> u8 {
    let mut v_name_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v_name_1060_ = lean_ctor_get(v_opt_1059_, 0);
    v_defValue_1061_ = lean_ctor_get(v_opt_1059_, 1);
    v_map_1062_ = lean_ctor_get(v_opts_1058_, 0);
    v___x_1063_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1062_,
            v_name_1060_,
        );
    if lean_obj_tag(v___x_1063_) == 0 {
        let mut v___x_1064_: u8 = 0;
        v___x_1064_ = (lean_unbox(v_defValue_1061_) as u8);
        return v___x_1064_;
    } else {
        let mut v_val_1065_: *mut LeanObject = core::ptr::null_mut();
        v_val_1065_ = lean_ctor_get(v___x_1063_, 0);
        lean_inc(v_val_1065_);
        lean_dec_ref_known(v___x_1063_, 1);
        if lean_obj_tag(v_val_1065_) == 1 {
            let mut v_v_1066_: u8 = 0;
            v_v_1066_ = lean_ctor_get_uint8(v_val_1065_, 0 as u32);
            lean_dec_ref_known(v_val_1065_, 0);
            return v_v_1066_;
        } else {
            let mut v___x_1067_: u8 = 0;
            lean_dec(v_val_1065_);
            v___x_1067_ = (lean_unbox(v_defValue_1061_) as u8);
            return v___x_1067_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10___boxed(
    mut v_opts_1068_: *mut LeanObject,
    mut v_opt_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1070_: u8 = 0;
    let mut v_r_1071_: *mut LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_1068_, v_opt_1069_);
    lean_dec_ref(v_opt_1069_);
    lean_dec_ref(v_opts_1068_);
    v_r_1071_ = lean_box((v_res_1070_) as usize);
    return v_r_1071_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1072_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___x_1073_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__0);
    v___x_1074_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1074_, 0, v___x_1073_);
    return v___x_1074_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    v___x_1075_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
    v___x_1076_ = lean_unsigned_to_nat(0);
    v___x_1077_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1077_, 0, v___x_1076_);
    lean_ctor_set(v___x_1077_, 1, v___x_1076_);
    lean_ctor_set(v___x_1077_, 2, v___x_1076_);
    lean_ctor_set(v___x_1077_, 3, v___x_1076_);
    lean_ctor_set(v___x_1077_, 4, v___x_1075_);
    lean_ctor_set(v___x_1077_, 5, v___x_1075_);
    lean_ctor_set(v___x_1077_, 6, v___x_1075_);
    lean_ctor_set(v___x_1077_, 7, v___x_1075_);
    lean_ctor_set(v___x_1077_, 8, v___x_1075_);
    lean_ctor_set(v___x_1077_, 9, v___x_1075_);
    return v___x_1077_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___x_1078_ = lean_unsigned_to_nat(32);
    v___x_1079_ = lean_mk_empty_array_with_capacity(v___x_1078_);
    v___x_1080_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    v___x_1081_ = 5usize;
    v___x_1082_ = lean_unsigned_to_nat(0);
    v___x_1083_ = lean_unsigned_to_nat(32);
    v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1083_);
    v___x_1085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__3);
    v___x_1086_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1086_, 0, v___x_1085_);
    lean_ctor_set(v___x_1086_, 1, v___x_1084_);
    lean_ctor_set(v___x_1086_, 2, v___x_1082_);
    lean_ctor_set(v___x_1086_, 3, v___x_1082_);
    lean_ctor_set_usize(v___x_1086_, 4, v___x_1081_);
    return v___x_1086_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_box(1);
    v___x_1088_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__4);
    v___x_1089_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__1);
    v___x_1090_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1090_, 0, v___x_1089_);
    lean_ctor_set(v___x_1090_, 1, v___x_1088_);
    lean_ctor_set(v___x_1090_, 2, v___x_1087_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(
    mut v_msgData_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v___x_1094_ = lean_st_ref_get(v___y_1092_);
    v_env_1095_ = lean_ctor_get(v___x_1094_, 0);
    lean_inc_ref(v_env_1095_);
    lean_dec(v___x_1094_);
    v___x_1096_ = lean_st_ref_get(v___y_1092_);
    v_scopes_1097_ = lean_ctor_get(v___x_1096_, 2);
    lean_inc(v_scopes_1097_);
    lean_dec(v___x_1096_);
    v___x_1098_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1099_ = l_List_head_x21___redArg(v___x_1098_, v_scopes_1097_);
    lean_dec(v_scopes_1097_);
    v_opts_1100_ = lean_ctor_get(v___x_1099_, 1);
    lean_inc_ref(v_opts_1100_);
    lean_dec(v___x_1099_);
    v___x_1101_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__2);
    v___x_1102_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___closed__5);
    v___x_1103_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1103_, 0, v_env_1095_);
    lean_ctor_set(v___x_1103_, 1, v___x_1101_);
    lean_ctor_set(v___x_1103_, 2, v___x_1102_);
    lean_ctor_set(v___x_1103_, 3, v_opts_1100_);
    v___x_1104_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    lean_ctor_set(v___x_1104_, 1, v_msgData_1091_);
    v___x_1105_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg___boxed(
    mut v_msgData_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_1106_, v___y_1107_);
    lean_dec(v___y_1107_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(
    mut v___y_1111_: u8,
    mut v_suppressElabErrors_1112_: u8,
    mut v_x_1113_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1113_) == 1 {
        let mut v_pre_1114_: *mut LeanObject = core::ptr::null_mut();
        v_pre_1114_ = lean_ctor_get(v_x_1113_, 0);
        if lean_obj_tag(v_pre_1114_) == 0 {
            let mut v_str_1115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: u8 = 0;
            v_str_1115_ = lean_ctor_get(v_x_1113_, 1);
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
    mut v___y_1118_: *mut LeanObject,
    mut v_suppressElabErrors_1119_: *mut LeanObject,
    mut v_x_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_26029__boxed_1121_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1122_: u8 = 0;
    let mut v_res_1123_: u8 = 0;
    let mut v_r_1124_: *mut LeanObject = core::ptr::null_mut();
    v___y_26029__boxed_1121_ = (lean_unbox(v___y_1118_) as u8);
    v_suppressElabErrors_boxed_1122_ = (lean_unbox(v_suppressElabErrors_1119_) as u8);
    v_res_1123_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0(v___y_26029__boxed_1121_, v_suppressElabErrors_boxed_1122_, v_x_1120_);
    lean_dec(v_x_1120_);
    v_r_1124_ = lean_box((v_res_1123_) as usize);
    return v_r_1124_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(
    mut v_ref_1126_: *mut LeanObject,
    mut v_msgData_1127_: *mut LeanObject,
    mut v_severity_1128_: u8,
    mut v_isSilent_1129_: u8,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1134_: u8 = 0;
    let mut v___y_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1136_: u8 = 0;
    let mut v___y_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_a_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1183_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut v_a_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v___y_1197_: u8 = 0;
    let mut v___y_1198_: u8 = 0;
    let mut v___y_1199_: u8 = 0;
    let mut v___y_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut v___y_1225_: u8 = 0;
    let mut v___y_1226_: u8 = 0;
    let mut v___y_1227_: u8 = 0;
    let mut v___y_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: u8 = 0;
    let mut v___y_1234_: u8 = 0;
    let mut v___y_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1245_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v___y_1252_: u8 = 0;
    let mut v___y_1253_: u8 = 0;
    let mut v___y_1254_: u8 = 0;
    let mut v___y_1256_: u8 = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: u8 = 0;
    let mut v___x_1263_: u8 = 0;
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: u8 = 0;
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_1127_);
                    v___x_1269_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1127_);
                    v___y_1256_ = v___x_1269_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1142_ = l_Lean_Elab_Command_getScope___redArg(v___y_1141_);
                if lean_obj_tag(v___x_1142_) == 0 {
                    v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
                    lean_inc(v_a_1143_);
                    lean_dec_ref_known(v___x_1142_, 1);
                    v___x_1144_ = l_Lean_Elab_Command_getScope___redArg(v___y_1141_);
                    if lean_obj_tag(v___x_1144_) == 0 {
                        v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
                        v_isSharedCheck_1179_ = (!lean_is_exclusive(v___x_1144_)) as u8;
                        if v_isSharedCheck_1179_ == 0 {
                            v___x_1147_ = v___x_1144_;
                            v_isShared_1148_ = v_isSharedCheck_1179_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1145_);
                            lean_dec(v___x_1144_);
                            v___x_1147_ = lean_box(0);
                            v_isShared_1148_ = v_isSharedCheck_1179_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1143_);
                        lean_dec(v___y_1140_);
                        lean_dec_ref(v___y_1137_);
                        lean_dec_ref(v___y_1135_);
                        v_a_1180_ = lean_ctor_get(v___x_1144_, 0);
                        v_isSharedCheck_1187_ = (!lean_is_exclusive(v___x_1144_)) as u8;
                        if v_isSharedCheck_1187_ == 0 {
                            v___x_1182_ = v___x_1144_;
                            v_isShared_1183_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1180_);
                            lean_dec(v___x_1144_);
                            v___x_1182_ = lean_box(0);
                            v_isShared_1183_ = v_isSharedCheck_1187_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1140_);
                    lean_dec_ref(v___y_1137_);
                    lean_dec_ref(v___y_1135_);
                    v_a_1188_ = lean_ctor_get(v___x_1142_, 0);
                    v_isSharedCheck_1195_ = (!lean_is_exclusive(v___x_1142_)) as u8;
                    if v_isSharedCheck_1195_ == 0 {
                        v___x_1190_ = v___x_1142_;
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1188_);
                        lean_dec(v___x_1142_);
                        v___x_1190_ = lean_box(0);
                        v_isShared_1191_ = v_isSharedCheck_1195_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1149_ = lean_st_ref_take(v___y_1141_);
                v_currNamespace_1150_ = lean_ctor_get(v_a_1143_, 2);
                lean_inc(v_currNamespace_1150_);
                lean_dec(v_a_1143_);
                v_openDecls_1151_ = lean_ctor_get(v_a_1145_, 3);
                lean_inc(v_openDecls_1151_);
                lean_dec(v_a_1145_);
                v_env_1152_ = lean_ctor_get(v___x_1149_, 0);
                v_messages_1153_ = lean_ctor_get(v___x_1149_, 1);
                v_scopes_1154_ = lean_ctor_get(v___x_1149_, 2);
                v_usedQuotCtxts_1155_ = lean_ctor_get(v___x_1149_, 3);
                v_nextMacroScope_1156_ = lean_ctor_get(v___x_1149_, 4);
                v_maxRecDepth_1157_ = lean_ctor_get(v___x_1149_, 5);
                v_ngen_1158_ = lean_ctor_get(v___x_1149_, 6);
                v_auxDeclNGen_1159_ = lean_ctor_get(v___x_1149_, 7);
                v_infoState_1160_ = lean_ctor_get(v___x_1149_, 8);
                v_traceState_1161_ = lean_ctor_get(v___x_1149_, 9);
                v_snapshotTasks_1162_ = lean_ctor_get(v___x_1149_, 10);
                v_isSharedCheck_1178_ = (!lean_is_exclusive(v___x_1149_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v___x_1164_ = v___x_1149_;
                    v_isShared_1165_ = v_isSharedCheck_1178_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1162_);
                    lean_inc(v_traceState_1161_);
                    lean_inc(v_infoState_1160_);
                    lean_inc(v_auxDeclNGen_1159_);
                    lean_inc(v_ngen_1158_);
                    lean_inc(v_maxRecDepth_1157_);
                    lean_inc(v_nextMacroScope_1156_);
                    lean_inc(v_usedQuotCtxts_1155_);
                    lean_inc(v_scopes_1154_);
                    lean_inc(v_messages_1153_);
                    lean_inc(v_env_1152_);
                    lean_dec(v___x_1149_);
                    v___x_1164_ = lean_box(0);
                    v_isShared_1165_ = v_isSharedCheck_1178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1166_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1166_, 0, v_currNamespace_1150_);
                lean_ctor_set(v___x_1166_, 1, v_openDecls_1151_);
                v___x_1167_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1167_, 0, v___x_1166_);
                lean_ctor_set(v___x_1167_, 1, v___y_1135_);
                lean_inc_ref(v___y_1138_);
                lean_inc_ref(v___y_1139_);
                v___x_1168_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_1168_, 0, v___y_1139_);
                lean_ctor_set(v___x_1168_, 1, v___y_1137_);
                lean_ctor_set(v___x_1168_, 2, v___y_1140_);
                lean_ctor_set(v___x_1168_, 3, v___y_1138_);
                lean_ctor_set(v___x_1168_, 4, v___x_1167_);
                lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_1134_,
                );
                lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_1136_,
                );
                lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1129_,
                );
                v___x_1169_ = l_Lean_MessageLog_add(v___x_1168_, v_messages_1153_);
                if v_isShared_1165_ == 0 {
                    lean_ctor_set(v___x_1164_, 1, v___x_1169_);
                    v___x_1171_ = v___x_1164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_env_1152_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1169_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_scopes_1154_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_usedQuotCtxts_1155_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_nextMacroScope_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_maxRecDepth_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_ngen_1158_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_auxDeclNGen_1159_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_infoState_1160_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_traceState_1161_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 10, v_snapshotTasks_1162_);
                    v___x_1171_ = v_reuseFailAlloc_1177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1172_ = lean_st_ref_set(v___y_1141_, v___x_1171_);
                v___x_1173_ = lean_box(0);
                if v_isShared_1148_ == 0 {
                    lean_ctor_set(v___x_1147_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1147_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
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
                    v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
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
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1193_;
            }
            10 => {
                v_fileName_1202_ = lean_ctor_get(v___y_1130_, 0);
                v_fileMap_1203_ = lean_ctor_get(v___y_1130_, 1);
                v_suppressElabErrors_1204_ = lean_ctor_get_uint8(
                    v___y_1130_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_1205_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1127_,
                    );
                v___x_1206_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v___x_1205_, v___y_1131_);
                v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
                v_isSharedCheck_1223_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                if v_isSharedCheck_1223_ == 0 {
                    v___x_1209_ = v___x_1206_;
                    v_isShared_1210_ = v_isSharedCheck_1223_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_1207_);
                    lean_dec(v___x_1206_);
                    v___x_1209_ = lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1223_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_1203_, 2);
                v___x_1211_ = l_Lean_FileMap_toPosition(v_fileMap_1203_, v___y_1200_);
                lean_dec(v___y_1200_);
                v___x_1212_ = l_Lean_FileMap_toPosition(v_fileMap_1203_, v___y_1201_);
                lean_dec(v___y_1201_);
                v___x_1213_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1213_, 0, v___x_1212_);
                v___x_1214_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___closed__0;
                if v_suppressElabErrors_1204_ == 0 {
                    lean_del_object(v___x_1209_);
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
                    v___x_1215_ = lean_box((v___y_1197_) as usize);
                    v___x_1216_ = lean_box((v_suppressElabErrors_1204_) as usize);
                    v___f_1217_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_1217_, 0, v___x_1215_);
                    lean_closure_set(v___f_1217_, 1, v___x_1216_);
                    lean_inc(v_a_1207_);
                    v___x_1218_ = l_Lean_MessageData_hasTag(v___f_1217_, v_a_1207_);
                    if v___x_1218_ == 0 {
                        lean_dec_ref_known(v___x_1213_, 1);
                        lean_dec_ref(v___x_1211_);
                        lean_dec(v_a_1207_);
                        v___x_1219_ = lean_box(0);
                        if v_isShared_1210_ == 0 {
                            lean_ctor_set(v___x_1209_, 0, v___x_1219_);
                            v___x_1221_ = v___x_1209_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
                            v___x_1221_ = v_reuseFailAlloc_1222_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1209_);
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
                lean_dec(v___y_1228_);
                if lean_obj_tag(v___x_1230_) == 0 {
                    lean_inc(v___y_1229_);
                    v___y_1197_ = v___y_1225_;
                    v___y_1198_ = v___y_1226_;
                    v___y_1199_ = v___y_1227_;
                    v___y_1200_ = v___y_1229_;
                    v___y_1201_ = v___y_1229_;
                    state = 10;
                    continue;
                } else {
                    v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
                    lean_inc(v_val_1231_);
                    lean_dec_ref_known(v___x_1230_, 1);
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
                if lean_obj_tag(v___x_1236_) == 0 {
                    v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
                    lean_inc(v_a_1237_);
                    lean_dec_ref_known(v___x_1236_, 1);
                    v_ref_1238_ = l_Lean_replaceRef(v_ref_1126_, v_a_1237_);
                    lean_dec(v_a_1237_);
                    v___x_1239_ = l_Lean_Syntax_getPos_x3f(v_ref_1238_, v___y_1234_);
                    if lean_obj_tag(v___x_1239_) == 0 {
                        v___x_1240_ = lean_unsigned_to_nat(0);
                        v___y_1225_ = v___y_1233_;
                        v___y_1226_ = v___y_1234_;
                        v___y_1227_ = v___y_1235_;
                        v___y_1228_ = v_ref_1238_;
                        v___y_1229_ = v___x_1240_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1241_ = lean_ctor_get(v___x_1239_, 0);
                        lean_inc(v_val_1241_);
                        lean_dec_ref_known(v___x_1239_, 1);
                        v___y_1225_ = v___y_1233_;
                        v___y_1226_ = v___y_1234_;
                        v___y_1227_ = v___y_1235_;
                        v___y_1228_ = v_ref_1238_;
                        v___y_1229_ = v_val_1241_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1127_);
                    v_a_1242_ = lean_ctor_get(v___x_1236_, 0);
                    v_isSharedCheck_1249_ = (!lean_is_exclusive(v___x_1236_)) as u8;
                    if v_isSharedCheck_1249_ == 0 {
                        v___x_1244_ = v___x_1236_;
                        v_isShared_1245_ = v_isSharedCheck_1249_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1242_);
                        lean_dec(v___x_1236_);
                        v___x_1244_ = lean_box(0);
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
                    v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
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
                    v_scopes_1258_ = lean_ctor_get(v___x_1257_, 2);
                    lean_inc(v_scopes_1258_);
                    lean_dec(v___x_1257_);
                    v___x_1259_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1260_ = l_List_head_x21___redArg(v___x_1259_, v_scopes_1258_);
                    lean_dec(v_scopes_1258_);
                    v_opts_1261_ = lean_ctor_get(v___x_1260_, 1);
                    lean_inc_ref(v_opts_1261_);
                    lean_dec(v___x_1260_);
                    v___x_1262_ = 1;
                    v___x_1263_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1128_, v___x_1262_);
                    if v___x_1263_ == 0 {
                        lean_dec_ref(v_opts_1261_);
                        v___y_1252_ = v___y_1256_;
                        v___y_1253_ = v___y_1256_;
                        v___y_1254_ = v___x_1263_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1264_ = l_Lean_warningAsError;
                        v___x_1265_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__10(v_opts_1261_, v___x_1264_);
                        lean_dec_ref(v_opts_1261_);
                        v___y_1252_ = v___y_1256_;
                        v___y_1253_ = v___y_1256_;
                        v___y_1254_ = v___x_1265_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_1127_);
                    v___x_1266_ = lean_box(0);
                    v___x_1267_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1267_, 0, v___x_1266_);
                    return v___x_1267_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6___boxed(
    mut v_ref_1270_: *mut LeanObject,
    mut v_msgData_1271_: *mut LeanObject,
    mut v_severity_1272_: *mut LeanObject,
    mut v_isSilent_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1277_: u8 = 0;
    let mut v_isSilent_boxed_1278_: u8 = 0;
    let mut v_res_1279_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1277_ = (lean_unbox(v_severity_1272_) as u8);
    v_isSilent_boxed_1278_ = (lean_unbox(v_isSilent_1273_) as u8);
    v_res_1279_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_1270_, v_msgData_1271_, v_severity_boxed_1277_, v_isSilent_boxed_1278_, v___y_1274_, v___y_1275_);
    lean_dec(v___y_1275_);
    lean_dec_ref(v___y_1274_);
    lean_dec(v_ref_1270_);
    return v_res_1279_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(
    mut v_ref_1280_: *mut LeanObject,
    mut v_msgData_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = 1;
    v___x_1286_ = 0;
    v___x_1287_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6(v_ref_1280_, v_msgData_1281_, v___x_1285_, v___x_1286_, v___y_1282_, v___y_1283_);
    return v___x_1287_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5___boxed(
    mut v_ref_1288_: *mut LeanObject,
    mut v_msgData_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1293_: *mut LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_ref_1288_, v_msgData_1289_, v___y_1290_, v___y_1291_);
    lean_dec(v___y_1291_);
    lean_dec_ref(v___y_1290_);
    lean_dec(v_ref_1288_);
    return v_res_1293_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__0;
    v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
    return v___x_1296_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ =
        l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__2;
    v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
    return v___x_1299_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
    mut v_linterOption_1300_: *mut LeanObject,
    mut v_stx_1301_: *mut LeanObject,
    mut v_msg_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_unused_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1306_ = lean_ctor_get(v_linterOption_1300_, 0);
                v_isSharedCheck_1323_ = (!lean_is_exclusive(v_linterOption_1300_)) as u8;
                if v_isSharedCheck_1323_ == 0 {
                    v_unused_1324_ = lean_ctor_get(v_linterOption_1300_, 1);
                    lean_dec(v_unused_1324_);
                    v___x_1308_ = v_linterOption_1300_;
                    v_isShared_1309_ = v_isSharedCheck_1323_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1306_);
                    lean_dec(v_linterOption_1300_);
                    v___x_1308_ = lean_box(0);
                    v_isShared_1309_ = v_isSharedCheck_1323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1310_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__1);
                lean_inc(v_name_1306_);
                v___x_1311_ = l_Lean_MessageData_ofName(v_name_1306_);
                if v_isShared_1309_ == 0 {
                    lean_ctor_set_tag(v___x_1308_, 7);
                    lean_ctor_set(v___x_1308_, 1, v___x_1311_);
                    lean_ctor_set(v___x_1308_, 0, v___x_1310_);
                    v___x_1313_ = v___x_1308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1310_);
                    lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1311_);
                    v___x_1313_ = v_reuseFailAlloc_1322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___closed__3);
                v___x_1315_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1315_, 0, v___x_1313_);
                lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                v_disable_1316_ = l_Lean_MessageData_note(v___x_1315_);
                v___x_1317_ = l_Lean_Linter_linterMessageTag;
                v___x_1318_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1318_, 0, v_msg_1302_);
                lean_ctor_set(v___x_1318_, 1, v_disable_1316_);
                v___x_1319_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1319_, 0, v___x_1317_);
                lean_ctor_set(v___x_1319_, 1, v___x_1318_);
                v___x_1320_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1320_, 0, v_name_1306_);
                lean_ctor_set(v___x_1320_, 1, v___x_1319_);
                v___x_1321_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5(v_stx_1301_, v___x_1320_, v___y_1303_, v___y_1304_);
                return v___x_1321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4___boxed(
    mut v_linterOption_1325_: *mut LeanObject,
    mut v_stx_1326_: *mut LeanObject,
    mut v_msg_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1331_: *mut LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
        v_linterOption_1325_,
        v_stx_1326_,
        v_msg_1327_,
        v___y_1328_,
        v___y_1329_,
    );
    lean_dec(v___y_1329_);
    lean_dec_ref(v___y_1328_);
    lean_dec(v_stx_1326_);
    return v_res_1331_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__1;
    v___x_1336_ = l_Lean_MessageData_ofFormat(v___x_1335_);
    return v___x_1336_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(
    mut v_as_1352_: *mut LeanObject,
    mut v_sz_1353_: usize,
    mut v_i_1354_: usize,
    mut v_b_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: usize = 0;
    let mut v___x_1362_: usize = 0;
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patHead_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1364_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
                if v___x_1364_ == 0 {
                    v___x_1365_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1365_, 0, v_b_1355_);
                    return v___x_1365_;
                } else {
                    v___x_1366_ = lean_box(0);
                    v_a_1374_ = lean_array_uget_borrowed(v_as_1352_, v_i_1354_);
                    v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__4;
                    lean_inc(v_a_1374_);
                    v___x_1376_ = l_Lean_Syntax_isOfKind(v_a_1374_, v___x_1375_);
                    if v___x_1376_ == 0 {
                        v_a_1360_ = v___x_1366_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1377_ = lean_unsigned_to_nat(1);
                        v___x_1378_ = l_Lean_Syntax_getArg(v_a_1374_, v___x_1377_);
                        v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__6;
                        lean_inc(v___x_1378_);
                        v___x_1380_ = l_Lean_Syntax_isOfKind(v___x_1378_, v___x_1379_);
                        if v___x_1380_ == 0 {
                            v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8;
                            lean_inc(v___x_1378_);
                            v___x_1382_ = l_Lean_Syntax_isOfKind(v___x_1378_, v___x_1381_);
                            if v___x_1382_ == 0 {
                                lean_dec(v___x_1378_);
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
                            v___x_1383_ = lean_unsigned_to_nat(0);
                            v___x_1384_ = l_Lean_Syntax_getArg(v___x_1378_, v___x_1383_);
                            lean_dec(v___x_1378_);
                            v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__8;
                            lean_inc(v___x_1384_);
                            v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
                            if v___x_1386_ == 0 {
                                lean_dec(v___x_1384_);
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
                v___x_1372_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5___closed__2);
                v___x_1373_ =
                    l_Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4(
                        v___x_1371_,
                        v_patHead_1368_,
                        v___x_1372_,
                        v___y_1369_,
                        v___y_1370_,
                    );
                lean_dec(v_patHead_1368_);
                if lean_obj_tag(v___x_1373_) == 0 {
                    lean_dec_ref_known(v___x_1373_, 1);
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
    mut v_as_1387_: *mut LeanObject,
    mut v_sz_1388_: *mut LeanObject,
    mut v_i_1389_: *mut LeanObject,
    mut v_b_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1394_: usize = 0;
    let mut v_i_boxed_1395_: usize = 0;
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1388_);
    lean_dec(v_sz_1388_);
    v_i_boxed_1395_ = lean_unbox_usize(v_i_1389_);
    lean_dec(v_i_1389_);
    v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_as_1387_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1390_, v___y_1391_, v___y_1392_);
    lean_dec(v___y_1392_);
    lean_dec_ref(v___y_1391_);
    lean_dec_ref(v_as_1387_);
    return v_res_1396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(
    mut v_sz_1403_: usize,
    mut v_i_1404_: usize,
    mut v_bs_1405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1406_ = lean_usize_dec_lt(v_i_1404_, v_sz_1403_);
                if v___x_1406_ == 0 {
                    v___x_1407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1407_, 0, v_bs_1405_);
                    return v___x_1407_;
                } else {
                    v_v_1408_ = lean_array_uget_borrowed(v_bs_1405_, v_i_1404_);
                    v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2___closed__1;
                    lean_inc(v_v_1408_);
                    v___x_1410_ = l_Lean_Syntax_isOfKind(v_v_1408_, v___x_1409_);
                    if v___x_1410_ == 0 {
                        lean_dec_ref(v_bs_1405_);
                        v___x_1411_ = lean_box(0);
                        return v___x_1411_;
                    } else {
                        v___x_1412_ = lean_unsigned_to_nat(1);
                        v___x_1413_ = l_Lean_Syntax_getArg(v_v_1408_, v___x_1412_);
                        lean_inc(v___x_1413_);
                        v___x_1414_ = l_Lean_Syntax_matchesNull(v___x_1413_, v___x_1412_);
                        if v___x_1414_ == 0 {
                            lean_dec(v___x_1413_);
                            lean_dec_ref(v_bs_1405_);
                            v___x_1415_ = lean_box(0);
                            return v___x_1415_;
                        } else {
                            v___x_1416_ = lean_unsigned_to_nat(0);
                            v___x_1417_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1416_);
                            lean_dec(v___x_1413_);
                            lean_inc(v___x_1417_);
                            v___x_1418_ = l_Lean_Syntax_matchesNull(v___x_1417_, v___x_1412_);
                            if v___x_1418_ == 0 {
                                lean_dec(v___x_1417_);
                                lean_dec_ref(v_bs_1405_);
                                v___x_1419_ = lean_box(0);
                                return v___x_1419_;
                            } else {
                                v_bs_x27_1420_ =
                                    lean_array_uset(v_bs_1405_, v_i_1404_, v___x_1416_);
                                v___x_1421_ = l_Lean_Syntax_getArg(v___x_1417_, v___x_1416_);
                                lean_dec(v___x_1417_);
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
    mut v_sz_1426_: *mut LeanObject,
    mut v_i_1427_: *mut LeanObject,
    mut v_bs_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1429_: usize = 0;
    let mut v_i_boxed_1430_: usize = 0;
    let mut v_res_1431_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1429_ = lean_unbox_usize(v_sz_1426_);
    lean_dec(v_sz_1426_);
    v_i_boxed_1430_ = lean_unbox_usize(v_i_1427_);
    lean_dec(v_i_1427_);
    v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_boxed_1429_, v_i_boxed_1430_, v_bs_1428_);
    return v_res_1431_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(
    mut v___x_1432_: u8,
    mut v_as_1433_: *mut LeanObject,
    mut v_i_1434_: usize,
    mut v_stop_1435_: usize,
    mut v_b_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v_fst_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v_snd_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_unused_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1442_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
                if v___x_1442_ == 0 {
                    v_fst_1443_ = lean_ctor_get(v_b_1436_, 0);
                    v___x_1444_ = (lean_unbox(v_fst_1443_) as u8);
                    if v___x_1444_ == 0 {
                        v_snd_1445_ = lean_ctor_get(v_b_1436_, 1);
                        v_isSharedCheck_1453_ = (!lean_is_exclusive(v_b_1436_)) as u8;
                        if v_isSharedCheck_1453_ == 0 {
                            v_unused_1454_ = lean_ctor_get(v_b_1436_, 0);
                            lean_dec(v_unused_1454_);
                            v___x_1447_ = v_b_1436_;
                            v_isShared_1448_ = v_isSharedCheck_1453_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_1445_);
                            lean_dec(v_b_1436_);
                            v___x_1447_ = lean_box(0);
                            v_isShared_1448_ = v_isSharedCheck_1453_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_1455_ = lean_ctor_get(v_b_1436_, 1);
                        v_isSharedCheck_1465_ = (!lean_is_exclusive(v_b_1436_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = lean_ctor_get(v_b_1436_, 0);
                            lean_dec(v_unused_1466_);
                            v___x_1457_ = v_b_1436_;
                            v_isShared_1458_ = v_isSharedCheck_1465_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_1455_);
                            lean_dec(v_b_1436_);
                            v___x_1457_ = lean_box(0);
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
                v___x_1449_ = lean_box((v___x_1432_) as usize);
                if v_isShared_1448_ == 0 {
                    lean_ctor_set(v___x_1447_, 0, v___x_1449_);
                    v___x_1451_ = v___x_1447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_snd_1445_);
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
                lean_inc(v___x_1459_);
                v___x_1460_ = lean_array_push(v_snd_1455_, v___x_1459_);
                v___x_1461_ = lean_box((v___x_1442_) as usize);
                if v_isShared_1458_ == 0 {
                    lean_ctor_set(v___x_1457_, 1, v___x_1460_);
                    lean_ctor_set(v___x_1457_, 0, v___x_1461_);
                    v___x_1463_ = v___x_1457_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1460_);
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
    mut v___x_1467_: *mut LeanObject,
    mut v_as_1468_: *mut LeanObject,
    mut v_i_1469_: *mut LeanObject,
    mut v_stop_1470_: *mut LeanObject,
    mut v_b_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_26559__boxed_1472_: u8 = 0;
    let mut v_i_boxed_1473_: usize = 0;
    let mut v_stop_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_26559__boxed_1472_ = (lean_unbox(v___x_1467_) as u8);
    v_i_boxed_1473_ = lean_unbox_usize(v_i_1469_);
    lean_dec(v_i_1469_);
    v_stop_boxed_1474_ = lean_unbox_usize(v_stop_1470_);
    lean_dec(v_stop_1470_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__6(v___x_26559__boxed_1472_, v_as_1468_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1471_);
    lean_dec_ref(v_as_1468_);
    return v_res_1475_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(
    mut v___x_1486_: u8,
    mut v_as_1487_: *mut LeanObject,
    mut v_i_1488_: usize,
    mut v_stop_1489_: usize,
) -> u8 {
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut v___y_1493_: u8 = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: usize = 0;
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc(v___x_1497_);
                    v___x_1499_ = l_Lean_Syntax_isOfKind(v___x_1497_, v___x_1498_);
                    if v___x_1499_ == 0 {
                        v___y_1493_ = v___x_1499_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1500_ = lean_unsigned_to_nat(0);
                        v___x_1501_ = l_Lean_Syntax_getArg(v___x_1497_, v___x_1500_);
                        v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3___closed__4;
                        v___x_1503_ = l_Lean_Syntax_matchesIdent(v___x_1501_, v___x_1502_);
                        lean_dec(v___x_1501_);
                        if v___x_1503_ == 0 {
                            v___y_1493_ = v___x_1503_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1504_ = lean_unsigned_to_nat(1);
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
    mut v___x_1508_: *mut LeanObject,
    mut v_as_1509_: *mut LeanObject,
    mut v_i_1510_: *mut LeanObject,
    mut v_stop_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_26644__boxed_1512_: u8 = 0;
    let mut v_i_boxed_1513_: usize = 0;
    let mut v_stop_boxed_1514_: usize = 0;
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_26644__boxed_1512_ = (lean_unbox(v___x_1508_) as u8);
    v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
    lean_dec(v_i_1510_);
    v_stop_boxed_1514_ = lean_unbox_usize(v_stop_1511_);
    lean_dec(v_stop_1511_);
    v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_26644__boxed_1512_, v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_);
    lean_dec_ref(v_as_1509_);
    v_r_1516_ = lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(
    mut v_cmdStx_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___y_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u8 = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1703_: usize = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1746_: usize = 0;
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut v_unused_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    let mut v___x_1778_: usize = 0;
    let mut v___x_1779_: usize = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: usize = 0;
    let mut v___x_1783_: usize = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1579_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0(v___y_1573_, v___y_1574_);
                v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
                v_isSharedCheck_1799_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                if v_isSharedCheck_1799_ == 0 {
                    v___x_1582_ = v___x_1579_;
                    v_isShared_1583_ = v_isSharedCheck_1799_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1580_);
                    lean_dec(v___x_1579_);
                    v___x_1582_ = lean_box(0);
                    v_isShared_1583_ = v_isSharedCheck_1799_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1577_ = lean_box(0);
                v___x_1578_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1578_, 0, v___x_1577_);
                return v___x_1578_;
            }
            2 => {
                v___x_1584_ = l_Lean_Linter_getLinterSuspiciousUnexpanderPatterns(v_a_1580_);
                lean_dec(v_a_1580_);
                if v___x_1584_ == 0 {
                    lean_dec(v_cmdStx_1572_);
                    v___x_1585_ = lean_box(0);
                    if v_isShared_1583_ == 0 {
                        lean_ctor_set(v___x_1582_, 0, v___x_1585_);
                        v___x_1587_ = v___x_1582_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
                        v___x_1587_ = v_reuseFailAlloc_1588_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1589_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_;
                    v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__0;
                    v___x_1591_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__2;
                    lean_inc(v_cmdStx_1572_);
                    v___x_1592_ = l_Lean_Syntax_isOfKind(v_cmdStx_1572_, v___x_1591_);
                    if v___x_1592_ == 0 {
                        lean_dec(v_cmdStx_1572_);
                        v___x_1593_ = lean_box(0);
                        if v_isShared_1583_ == 0 {
                            lean_ctor_set(v___x_1582_, 0, v___x_1593_);
                            v___x_1595_ = v___x_1582_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
                            v___x_1595_ = v_reuseFailAlloc_1596_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1597_ = lean_unsigned_to_nat(0);
                        v___x_1598_ = l_Lean_Syntax_getArg(v_cmdStx_1572_, v___x_1597_);
                        v___x_1599_ =
                            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__4;
                        lean_inc(v___x_1598_);
                        v___x_1600_ = l_Lean_Syntax_isOfKind(v___x_1598_, v___x_1599_);
                        if v___x_1600_ == 0 {
                            lean_dec(v___x_1598_);
                            lean_del_object(v___x_1582_);
                            lean_dec(v_cmdStx_1572_);
                            v___x_1786_ = lean_box(0);
                            v___x_1787_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1787_, 0, v___x_1786_);
                            return v___x_1787_;
                        } else {
                            v___x_1788_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1597_);
                            v___x_1789_ = l_Lean_Syntax_isNone(v___x_1788_);
                            if v___x_1789_ == 0 {
                                v___x_1790_ = lean_unsigned_to_nat(1);
                                lean_inc(v___x_1788_);
                                v___x_1791_ = l_Lean_Syntax_matchesNull(v___x_1788_, v___x_1790_);
                                if v___x_1791_ == 0 {
                                    lean_dec(v___x_1788_);
                                    lean_dec(v___x_1598_);
                                    lean_del_object(v___x_1582_);
                                    lean_dec(v_cmdStx_1572_);
                                    v___x_1792_ = lean_box(0);
                                    v___x_1793_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                                    return v___x_1793_;
                                } else {
                                    v___x_1794_ = l_Lean_Syntax_getArg(v___x_1788_, v___x_1597_);
                                    lean_dec(v___x_1788_);
                                    v___x_1795_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__21;
                                    v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
                                    if v___x_1796_ == 0 {
                                        lean_dec(v___x_1598_);
                                        lean_del_object(v___x_1582_);
                                        lean_dec(v_cmdStx_1572_);
                                        v___x_1797_ = lean_box(0);
                                        v___x_1798_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1798_, 0, v___x_1797_);
                                        return v___x_1798_;
                                    } else {
                                        v___y_1757_ = v___y_1573_;
                                        v___y_1758_ = v___y_1574_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_1788_);
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
                if lean_obj_tag(v___x_1609_) == 0 {
                    lean_dec(v___x_1598_);
                    lean_dec(v_cmdStx_1572_);
                    v___x_1610_ = lean_box(0);
                    if v_isShared_1583_ == 0 {
                        lean_ctor_set(v___x_1582_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1582_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_val_1614_ = lean_ctor_get(v___x_1609_, 0);
                    lean_inc(v_val_1614_);
                    lean_dec_ref_known(v___x_1609_, 1);
                    v___x_1615_ = lean_unsigned_to_nat(3);
                    v___x_1616_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1615_);
                    v___x_1617_ = l_Lean_Syntax_matchesNull(v___x_1616_, v___x_1597_);
                    if v___x_1617_ == 0 {
                        lean_dec(v_val_1614_);
                        lean_dec(v___x_1598_);
                        lean_dec(v_cmdStx_1572_);
                        v___x_1618_ = lean_box(0);
                        if v_isShared_1583_ == 0 {
                            lean_ctor_set(v___x_1582_, 0, v___x_1618_);
                            v___x_1620_ = v___x_1582_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
                            v___x_1620_ = v_reuseFailAlloc_1621_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_1622_ = lean_unsigned_to_nat(4);
                        v___x_1623_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1622_);
                        v___x_1624_ = l_Lean_Syntax_matchesNull(v___x_1623_, v___x_1597_);
                        if v___x_1624_ == 0 {
                            lean_dec(v_val_1614_);
                            lean_dec(v___x_1598_);
                            lean_dec(v_cmdStx_1572_);
                            v___x_1625_ = lean_box(0);
                            if v_isShared_1583_ == 0 {
                                lean_ctor_set(v___x_1582_, 0, v___x_1625_);
                                v___x_1627_ = v___x_1582_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
                                v___x_1627_ = v_reuseFailAlloc_1628_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_1629_ = lean_unsigned_to_nat(5);
                            v___x_1630_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1629_);
                            v___x_1631_ = l_Lean_Syntax_matchesNull(v___x_1630_, v___x_1597_);
                            if v___x_1631_ == 0 {
                                lean_dec(v_val_1614_);
                                lean_dec(v___x_1598_);
                                lean_dec(v_cmdStx_1572_);
                                v___x_1632_ = lean_box(0);
                                if v_isShared_1583_ == 0 {
                                    lean_ctor_set(v___x_1582_, 0, v___x_1632_);
                                    v___x_1634_ = v___x_1582_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
                                    v___x_1634_ = v_reuseFailAlloc_1635_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v___x_1636_ = lean_unsigned_to_nat(6);
                                v___x_1637_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1636_);
                                lean_dec(v___x_1598_);
                                v___x_1638_ = l_Lean_Syntax_matchesNull(v___x_1637_, v___x_1597_);
                                if v___x_1638_ == 0 {
                                    lean_dec(v_val_1614_);
                                    lean_dec(v_cmdStx_1572_);
                                    v___x_1639_ = lean_box(0);
                                    if v_isShared_1583_ == 0 {
                                        lean_ctor_set(v___x_1582_, 0, v___x_1639_);
                                        v___x_1641_ = v___x_1582_;
                                        state = 10;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
                                        v___x_1641_ = v_reuseFailAlloc_1642_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    v___x_1643_ = l_Lean_Syntax_getArg(v_cmdStx_1572_, v___y_1605_);
                                    lean_dec(v_cmdStx_1572_);
                                    v___x_1644_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__6;
                                    lean_inc(v___x_1643_);
                                    v___x_1645_ = l_Lean_Syntax_isOfKind(v___x_1643_, v___x_1644_);
                                    if v___x_1645_ == 0 {
                                        lean_dec(v___x_1643_);
                                        lean_dec(v_val_1614_);
                                        v___x_1646_ = lean_box(0);
                                        if v_isShared_1583_ == 0 {
                                            lean_ctor_set(v___x_1582_, 0, v___x_1646_);
                                            v___x_1648_ = v___x_1582_;
                                            state = 11;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1649_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
                                            v___x_1648_ = v_reuseFailAlloc_1649_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v___x_1650_ = lean_unsigned_to_nat(2);
                                        v___x_1651_ =
                                            l_Lean_Syntax_getArg(v___x_1643_, v___x_1650_);
                                        v___x_1652_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__8;
                                        lean_inc(v___x_1651_);
                                        v___x_1653_ =
                                            l_Lean_Syntax_isOfKind(v___x_1651_, v___x_1652_);
                                        if v___x_1653_ == 0 {
                                            lean_dec(v___x_1651_);
                                            lean_dec(v___x_1643_);
                                            lean_dec(v_val_1614_);
                                            v___x_1654_ = lean_box(0);
                                            if v_isShared_1583_ == 0 {
                                                lean_ctor_set(v___x_1582_, 0, v___x_1654_);
                                                v___x_1656_ = v___x_1582_;
                                                state = 12;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_1657_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
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
                                                lean_dec(v___x_1651_);
                                                lean_dec(v___x_1643_);
                                                lean_dec(v_val_1614_);
                                                v___x_1660_ = lean_box(0);
                                                if v_isShared_1583_ == 0 {
                                                    lean_ctor_set(v___x_1582_, 0, v___x_1660_);
                                                    v___x_1662_ = v___x_1582_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_1663_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
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
                                                lean_dec(v___x_1651_);
                                                lean_inc(v___x_1664_);
                                                v___x_1665_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1664_,
                                                    v___y_1605_,
                                                );
                                                if v___x_1665_ == 0 {
                                                    lean_dec(v___x_1664_);
                                                    lean_dec(v___x_1643_);
                                                    lean_dec(v_val_1614_);
                                                    v___x_1666_ = lean_box(0);
                                                    if v_isShared_1583_ == 0 {
                                                        lean_ctor_set(v___x_1582_, 0, v___x_1666_);
                                                        v___x_1668_ = v___x_1582_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_1669_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(
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
                                                    lean_dec(v___x_1664_);
                                                    v___x_1671_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__9;
                                                    lean_inc_ref(v___y_1602_);
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
                                                    lean_dec(v___x_1672_);
                                                    if v___x_1673_ == 0 {
                                                        lean_dec(v___x_1643_);
                                                        lean_dec(v_val_1614_);
                                                        v___x_1674_ = lean_box(0);
                                                        if v_isShared_1583_ == 0 {
                                                            lean_ctor_set(
                                                                v___x_1582_,
                                                                0,
                                                                v___x_1674_,
                                                            );
                                                            v___x_1676_ = v___x_1582_;
                                                            state = 15;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_1677_ =
                                                                lean_alloc_ctor(0, 1, (0) as u32);
                                                            lean_ctor_set(
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
                                                        lean_inc(v___x_1678_);
                                                        v___x_1680_ = l_Lean_Syntax_isOfKind(
                                                            v___x_1678_,
                                                            v___x_1679_,
                                                        );
                                                        if v___x_1680_ == 0 {
                                                            lean_dec(v___x_1678_);
                                                            lean_dec(v___x_1643_);
                                                            lean_dec(v_val_1614_);
                                                            v___x_1681_ = lean_box(0);
                                                            if v_isShared_1583_ == 0 {
                                                                lean_ctor_set(
                                                                    v___x_1582_,
                                                                    0,
                                                                    v___x_1681_,
                                                                );
                                                                v___x_1683_ = v___x_1582_;
                                                                state = 16;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_1684_ =
                                                                    lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                lean_ctor_set(
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
                                                            lean_dec(v___x_1678_);
                                                            v___x_1686_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__12;
                                                            lean_inc_ref(v___y_1602_);
                                                            v___x_1687_ = l_Lean_Name_mkStr4(
                                                                v___x_1589_,
                                                                v___x_1590_,
                                                                v___y_1602_,
                                                                v___x_1686_,
                                                            );
                                                            lean_inc(v___x_1685_);
                                                            v___x_1688_ = l_Lean_Syntax_isOfKind(
                                                                v___x_1685_,
                                                                v___x_1687_,
                                                            );
                                                            lean_dec(v___x_1687_);
                                                            if v___x_1688_ == 0 {
                                                                lean_dec(v___x_1685_);
                                                                lean_dec(v___x_1643_);
                                                                lean_dec(v_val_1614_);
                                                                v___x_1689_ = lean_box(0);
                                                                if v_isShared_1583_ == 0 {
                                                                    lean_ctor_set(
                                                                        v___x_1582_,
                                                                        0,
                                                                        v___x_1689_,
                                                                    );
                                                                    v___x_1691_ = v___x_1582_;
                                                                    state = 17;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_1692_ =
                                                                        lean_alloc_ctor(
                                                                            0,
                                                                            1,
                                                                            (0) as u32,
                                                                        );
                                                                    lean_ctor_set(
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
                                                                lean_inc_ref(v___y_1602_);
                                                                v___x_1695_ = l_Lean_Name_mkStr4(
                                                                    v___x_1589_,
                                                                    v___x_1590_,
                                                                    v___y_1602_,
                                                                    v___x_1694_,
                                                                );
                                                                lean_inc(v___x_1693_);
                                                                v___x_1696_ =
                                                                    l_Lean_Syntax_isOfKind(
                                                                        v___x_1693_,
                                                                        v___x_1695_,
                                                                    );
                                                                lean_dec(v___x_1695_);
                                                                if v___x_1696_ == 0 {
                                                                    lean_dec(v___x_1693_);
                                                                    lean_dec(v___x_1685_);
                                                                    lean_dec(v___x_1643_);
                                                                    lean_dec(v_val_1614_);
                                                                    v___x_1697_ = lean_box(0);
                                                                    if v_isShared_1583_ == 0 {
                                                                        lean_ctor_set(
                                                                            v___x_1582_,
                                                                            0,
                                                                            v___x_1697_,
                                                                        );
                                                                        v___x_1699_ = v___x_1582_;
                                                                        state = 18;
                                                                        continue;
                                                                    } else {
                                                                        v_reuseFailAlloc_1700_ =
                                                                            lean_alloc_ctor(
                                                                                0,
                                                                                1,
                                                                                (0) as u32,
                                                                            );
                                                                        lean_ctor_set(
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
                                                                    lean_dec(v___x_1693_);
                                                                    v___x_1702_ =
                                                                        l_Lean_Syntax_getArgs(
                                                                            v___x_1701_,
                                                                        );
                                                                    lean_dec(v___x_1701_);
                                                                    v_sz_1703_ = lean_array_size(
                                                                        v___x_1702_,
                                                                    );
                                                                    v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__2(v_sz_1703_, v___x_1608_, v___x_1702_);
                                                                    if lean_obj_tag(v___x_1704_)
                                                                        == 0
                                                                    {
                                                                        lean_dec(v___x_1685_);
                                                                        lean_dec(v___x_1643_);
                                                                        lean_dec(v_val_1614_);
                                                                        v___x_1705_ = lean_box(0);
                                                                        if v_isShared_1583_ == 0 {
                                                                            lean_ctor_set(
                                                                                v___x_1582_,
                                                                                0,
                                                                                v___x_1705_,
                                                                            );
                                                                            v___x_1707_ =
                                                                                v___x_1582_;
                                                                            state = 19;
                                                                            continue;
                                                                        } else {
                                                                            v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                                            lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
                                                                            v___x_1707_ = v_reuseFailAlloc_1708_;
                                                                            state = 19;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_val_1709_ = lean_ctor_get(
                                                                            v___x_1704_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_val_1709_);
                                                                        lean_dec_ref_known(
                                                                            v___x_1704_,
                                                                            1,
                                                                        );
                                                                        v___x_1710_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v___x_1685_,
                                                                                v___y_1605_,
                                                                            );
                                                                        v___x_1711_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__16;
                                                                        lean_inc(v___x_1710_);
                                                                        v___x_1712_ =
                                                                            l_Lean_Syntax_isOfKind(
                                                                                v___x_1710_,
                                                                                v___x_1711_,
                                                                            );
                                                                        if v___x_1712_ == 0 {
                                                                            lean_dec(v___x_1710_);
                                                                            lean_dec(v_val_1709_);
                                                                            lean_dec(v___x_1685_);
                                                                            lean_dec(v___x_1643_);
                                                                            lean_dec(v_val_1614_);
                                                                            v___x_1713_ =
                                                                                lean_box(0);
                                                                            if v_isShared_1583_ == 0
                                                                            {
                                                                                lean_ctor_set(
                                                                                    v___x_1582_,
                                                                                    0,
                                                                                    v___x_1713_,
                                                                                );
                                                                                v___x_1715_ =
                                                                                    v___x_1582_;
                                                                                state = 20;
                                                                                continue;
                                                                            } else {
                                                                                v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                                                lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
                                                                                v___x_1715_ = v_reuseFailAlloc_1716_;
                                                                                state = 20;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            v___x_1717_ = l_Lean_Syntax_getArg(v___x_1710_, v___x_1597_);
                                                                            v___x_1718_ = l_Lean_Syntax_matchesNull(v___x_1717_, v___x_1597_);
                                                                            if v___x_1718_ == 0 {
                                                                                lean_dec(
                                                                                    v___x_1710_,
                                                                                );
                                                                                lean_dec(
                                                                                    v_val_1709_,
                                                                                );
                                                                                lean_dec(
                                                                                    v___x_1685_,
                                                                                );
                                                                                lean_dec(
                                                                                    v___x_1643_,
                                                                                );
                                                                                lean_dec(
                                                                                    v_val_1614_,
                                                                                );
                                                                                v___x_1719_ =
                                                                                    lean_box(0);
                                                                                if v_isShared_1583_
                                                                                    == 0
                                                                                {
                                                                                    lean_ctor_set(
                                                                                        v___x_1582_,
                                                                                        0,
                                                                                        v___x_1719_,
                                                                                    );
                                                                                    v___x_1721_ =
                                                                                        v___x_1582_;
                                                                                    state = 21;
                                                                                    continue;
                                                                                } else {
                                                                                    v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                                                    lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                                                                                    v___x_1721_ = v_reuseFailAlloc_1722_;
                                                                                    state = 21;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                v___x_1723_ = l_Lean_Syntax_getArg(v___x_1710_, v___y_1605_);
                                                                                lean_dec(
                                                                                    v___x_1710_,
                                                                                );
                                                                                v___x_1724_ = l_Lean_Syntax_matchesNull(v___x_1723_, v___x_1597_);
                                                                                if v___x_1724_ == 0
                                                                                {
                                                                                    lean_dec(
                                                                                        v_val_1709_,
                                                                                    );
                                                                                    lean_dec(
                                                                                        v___x_1685_,
                                                                                    );
                                                                                    lean_dec(
                                                                                        v___x_1643_,
                                                                                    );
                                                                                    lean_dec(
                                                                                        v_val_1614_,
                                                                                    );
                                                                                    v___x_1725_ =
                                                                                        lean_box(0);
                                                                                    if v_isShared_1583_ == 0 {
lean_ctor_set(v___x_1582_, 0, v___x_1725_);
v___x_1727_ = v___x_1582_;
state = 22; continue;
} else {
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
state = 22; continue;
}
                                                                                } else {
                                                                                    v___x_1729_ = l_Lean_Syntax_getArg(v___x_1685_, v___x_1650_);
                                                                                    lean_dec(
                                                                                        v___x_1685_,
                                                                                    );
                                                                                    v___x_1730_ = l_Lean_Syntax_matchesNull(v___x_1729_, v___x_1597_);
                                                                                    if v___x_1730_
                                                                                        == 0
                                                                                    {
                                                                                        lean_dec(v_val_1709_);
                                                                                        lean_dec(v___x_1643_);
                                                                                        lean_dec(v_val_1614_);
                                                                                        v___x_1731_ = lean_box(0);
                                                                                        if v_isShared_1583_ == 0 {
lean_ctor_set(v___x_1582_, 0, v___x_1731_);
v___x_1733_ = v___x_1582_;
state = 23; continue;
} else {
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
state = 23; continue;
}
                                                                                    } else {
                                                                                        v___x_1735_ = l_Lean_Syntax_getArg(v___x_1643_, v___x_1622_);
                                                                                        lean_dec(v___x_1643_);
                                                                                        v___x_1736_ = l_Lean_Syntax_matchesNull(v___x_1735_, v___x_1597_);
                                                                                        if v___x_1736_ == 0 {
lean_dec(v_val_1709_);
lean_dec(v_val_1614_);
v___x_1737_ = lean_box(0);
if v_isShared_1583_ == 0 {
lean_ctor_set(v___x_1582_, 0, v___x_1737_);
v___x_1739_ = v___x_1582_;
state = 24; continue;
} else {
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
state = 24; continue;
}
} else {
lean_del_object(v___x_1582_);
v___x_1741_ = lean_array_get_size(v_val_1614_);
v___x_1742_ = lean_nat_dec_lt(v___x_1597_, v___x_1741_);
if v___x_1742_ == 0 {
lean_dec(v_val_1709_);
lean_dec(v_val_1614_);
state = 1; continue;
} else {
if v___x_1742_ == 0 {
lean_dec(v_val_1709_);
lean_dec(v_val_1614_);
state = 1; continue;
} else {
v___x_1743_ = lean_usize_of_nat(v___x_1741_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__3(v___x_1600_, v_val_1614_, v___x_1608_, v___x_1743_);
lean_dec(v_val_1614_);
if v___x_1744_ == 0 {
lean_dec(v_val_1709_);
state = 1; continue;
} else {
v___x_1745_ = lean_box(0);
v_sz_1746_ = lean_array_size(v_val_1709_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__5(v_val_1709_, v_sz_1746_, v___x_1608_, v___x_1745_, v___y_1603_, v___y_1604_);
lean_dec(v_val_1709_);
if lean_obj_tag(v___x_1747_) == 0 {
v_isSharedCheck_1754_ = (!lean_is_exclusive(v___x_1747_)) as u8;
if v_isSharedCheck_1754_ == 0 {
v_unused_1755_ = lean_ctor_get(v___x_1747_, 0);
lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1747_;
v_isShared_1750_ = v_isSharedCheck_1754_;
state = 25; continue;
} else {
lean_dec(v___x_1747_);
v___x_1749_ = lean_box(0);
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
                    lean_ctor_set(v___x_1749_, 0, v___x_1745_);
                    v___x_1752_ = v___x_1749_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1745_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1752_;
            }
            27 => {
                v___x_1759_ = lean_unsigned_to_nat(1);
                v___x_1760_ = l_Lean_Syntax_getArg(v___x_1598_, v___x_1759_);
                lean_inc(v___x_1760_);
                v___x_1761_ = l_Lean_Syntax_matchesNull(v___x_1760_, v___x_1759_);
                if v___x_1761_ == 0 {
                    lean_dec(v___x_1760_);
                    lean_dec(v___x_1598_);
                    lean_del_object(v___x_1582_);
                    lean_dec(v_cmdStx_1572_);
                    v___x_1762_ = lean_box(0);
                    v___x_1763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                } else {
                    v___x_1764_ = l_Lean_Syntax_getArg(v___x_1760_, v___x_1597_);
                    lean_dec(v___x_1760_);
                    v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__1___closed__1;
                    v___x_1766_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__18;
                    lean_inc(v___x_1764_);
                    v___x_1767_ = l_Lean_Syntax_isOfKind(v___x_1764_, v___x_1766_);
                    if v___x_1767_ == 0 {
                        lean_dec(v___x_1764_);
                        lean_dec(v___x_1598_);
                        lean_del_object(v___x_1582_);
                        lean_dec(v_cmdStx_1572_);
                        v___x_1768_ = lean_box(0);
                        v___x_1769_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                        return v___x_1769_;
                    } else {
                        v___x_1770_ = l_Lean_Syntax_getArg(v___x_1764_, v___x_1759_);
                        lean_dec(v___x_1764_);
                        v___x_1771_ = l_Lean_Syntax_getArgs(v___x_1770_);
                        lean_dec(v___x_1770_);
                        v___x_1772_ =
                            l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0___closed__19;
                        v___x_1773_ = lean_array_get_size(v___x_1771_);
                        v___x_1774_ = lean_nat_dec_lt(v___x_1597_, v___x_1773_);
                        if v___x_1774_ == 0 {
                            lean_dec_ref(v___x_1771_);
                            v___y_1602_ = v___x_1765_;
                            v___y_1603_ = v___y_1757_;
                            v___y_1604_ = v___y_1758_;
                            v___y_1605_ = v___x_1759_;
                            v___y_1606_ = v___x_1772_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1775_ = lean_box((v___x_1767_) as usize);
                            v___x_1776_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1776_, 0, v___x_1775_);
                            lean_ctor_set(v___x_1776_, 1, v___x_1772_);
                            v___x_1777_ = lean_nat_dec_le(v___x_1773_, v___x_1773_);
                            if v___x_1777_ == 0 {
                                if v___x_1774_ == 0 {
                                    lean_dec_ref_known(v___x_1776_, 2);
                                    lean_dec_ref(v___x_1771_);
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
                                    lean_dec_ref(v___x_1771_);
                                    v_snd_1781_ = lean_ctor_get(v___x_1780_, 1);
                                    lean_inc(v_snd_1781_);
                                    lean_dec_ref(v___x_1780_);
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
                                lean_dec_ref(v___x_1771_);
                                v_snd_1785_ = lean_ctor_get(v___x_1784_, 1);
                                lean_inc(v_snd_1785_);
                                lean_dec_ref(v___x_1784_);
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
    mut v_cmdStx_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1804_: *mut LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Lean_Linter_suspiciousUnexpanderPatterns___lam__0(
        v_cmdStx_1800_,
        v___y_1801_,
        v___y_1802_,
    );
    lean_dec(v___y_1802_);
    lean_dec_ref(v___y_1801_);
    return v_res_1804_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(
    mut v_o_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___redArg(v_o_1814_, v___y_1816_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0___boxed(
    mut v_o_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1823_: *mut LeanObject = core::ptr::null_mut();
    v_res_1823_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__0_spec__0(v_o_1819_, v___y_1820_, v___y_1821_);
    lean_dec(v___y_1821_);
    lean_dec_ref(v___y_1820_);
    return v_res_1823_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(
    mut v_msgData_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___redArg(v_msgData_1824_, v___y_1826_);
    return v___x_1828_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9___boxed(
    mut v_msgData_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_suspiciousUnexpanderPatterns_spec__4_spec__5_spec__6_spec__9(v_msgData_1829_, v___y_1830_, v___y_1831_);
    lean_dec(v___y_1831_);
    lean_dec_ref(v___y_1830_);
    return v_res_1833_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_Linter_suspiciousUnexpanderPatterns;
    v___x_1836_ = l_Lean_Elab_Command_addLinter(v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2____boxed(
    mut v_a_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1838_ = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
    return v_res_1838_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Builtin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1271794952____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_suspiciousUnexpanderPatterns = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_suspiciousUnexpanderPatterns);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Builtin_0__Lean_Linter_initFn_00___x40_Lean_Linter_Builtin_1774244096____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Builtin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Builtin(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Builtin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Builtin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Builtin(builtin);
}
