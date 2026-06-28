// Lean compiler output
// Module: Lean.Linter.CheckUnivs
// Imports: Lean.Linter.Basic Lean.Linter.Util Lean.Util.CollectLevelParams Lean.Util.ForEachExpr
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::System::ST::l_runST___redArg;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_addLinter, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::l_Lean_Expr_hash;
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, l_Lean_Linter_getNewDecls, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_MessageLog_hasErrors,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, l_Lean_CollectLevelParams_visitLevel,
    runtime_initialize_Lean_Util_CollectLevelParams,
};
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 85, 110, 105, 118, 115, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16210467313202055922 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<176> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 176, m_capacity: 176, m_length: 175, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 96, 99, 104, 101, 99, 107, 85, 110, 105, 118, 115, 96, 32, 108, 105, 110, 116, 101, 114, 44, 32, 119, 104, 105, 99, 104, 32, 119, 97, 114, 110, 115, 32, 119, 104, 101, 110, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 104, 97, 115, 32, 97, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 116, 104, 97, 116, 32, 111, 110, 108, 121, 32, 101, 118, 101, 114, 32, 111, 99, 99, 117, 114, 115, 32, 105, 110, 32, 97, 32, 96, 109, 97, 120, 32, 117, 32, 118, 96, 32, 116, 111, 103, 101, 116, 104, 101, 114, 32, 119, 105, 116, 104, 32, 97, 110, 111, 116, 104, 101, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 44, 32, 110, 101, 118, 101, 114, 32, 111, 110, 32, 105, 116, 115, 32, 111, 119, 110, 46, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12426330975265000841 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0: u64 = 0;
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 95, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [96, 58, 32, 117, 110, 105, 118, 101, 114, 115, 101, 115, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5_value: crate::leanh::LeanStringObject<132> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 132, m_capacity: 132, m_length: 131, m_data: [32, 111, 110, 108, 121, 32, 111, 99, 99, 117, 114, 32, 116, 111, 103, 101, 116, 104, 101, 114, 46, 32, 84, 104, 105, 115, 32, 117, 115, 117, 97, 108, 108, 121, 32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 97, 32, 96, 109, 97, 120, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 119, 104, 101, 114, 101, 32, 110, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 115, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 115, 32, 97, 112, 112, 101, 97, 114, 32, 111, 110, 32, 116, 104, 101, 105, 114, 32, 111, 119, 110, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value:
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
    m_fun: l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value:
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
    m_data: [67, 104, 101, 99, 107, 85, 110, 105, 118, 115, 0],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 104, 101, 99, 107, 85, 110, 105, 118, 115, 76, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17211735266089129274 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7222886008983397929 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(
    mut v_name_1805_: *mut crate::leanh::LeanObject,
    mut v_decl_1806_: *mut crate::leanh::LeanObject,
    mut v_ref_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_unused_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1809_ = crate::leanh::lean_ctor_get(v_decl_1806_, 0);
                v_descr_1810_ = crate::leanh::lean_ctor_get(v_decl_1806_, 1);
                v_deprecation_x3f_1811_ = crate::leanh::lean_ctor_get(v_decl_1806_, 2);
                v___x_1812_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1813_ = (crate::leanh::lean_unbox(v_defValue_1809_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_1812_, 0 as u32, v___x_1813_);
                crate::leanh::lean_inc(v_deprecation_x3f_1811_);
                crate::leanh::lean_inc_ref(v_descr_1810_);
                crate::leanh::lean_inc_n(v_name_1805_, 2);
                v___x_1814_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1814_, 0, v_name_1805_);
                crate::leanh::lean_ctor_set(v___x_1814_, 1, v_ref_1807_);
                crate::leanh::lean_ctor_set(v___x_1814_, 2, v___x_1812_);
                crate::leanh::lean_ctor_set(v___x_1814_, 3, v_descr_1810_);
                crate::leanh::lean_ctor_set(v___x_1814_, 4, v_deprecation_x3f_1811_);
                v___x_1815_ = lean_register_option(v_name_1805_, v___x_1814_);
                if crate::leanh::lean_obj_tag(v___x_1815_) == 0 {
                    v_isSharedCheck_1823_ = (!crate::leanh::lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v_unused_1824_ = crate::leanh::lean_ctor_get(v___x_1815_, 0);
                        crate::leanh::lean_dec(v_unused_1824_);
                        v___x_1817_ = v___x_1815_;
                        v_isShared_1818_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1815_);
                        v___x_1817_ = crate::leanh::lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1805_);
                    v_a_1825_ = crate::leanh::lean_ctor_get(v___x_1815_, 0);
                    v_isSharedCheck_1832_ = (!crate::leanh::lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1832_ == 0 {
                        v___x_1827_ = v___x_1815_;
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1825_);
                        crate::leanh::lean_dec(v___x_1815_);
                        v___x_1827_ = crate::leanh::lean_box(0);
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_1809_);
                v___x_1819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1819_, 0, v_name_1805_);
                crate::leanh::lean_ctor_set(v___x_1819_, 1, v_defValue_1809_);
                if v_isShared_1818_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1817_, 0, v___x_1819_);
                    v___x_1821_ = v___x_1817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1821_;
            }
            3 => {
                if v_isShared_1828_ == 0 {
                    v___x_1830_ = v___x_1827_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1833_: *mut crate::leanh::LeanObject,
    mut v_decl_1834_: *mut crate::leanh::LeanObject,
    mut v_ref_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(v_name_1833_, v_decl_1834_, v_ref_1835_);
    crate::leanh::lean_dec_ref(v_decl_1834_);
    return v_res_1837_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1858_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1859_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1860_ = l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(v___x_1857_, v___x_1858_, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4____boxed(
    mut v_a_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_();
    return v_res_1862_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0()
-> u64 {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u64 = 0;
    v___x_1863_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1864_ = lean_uint64_of_nat(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(
    mut v_as_1865_: *mut crate::leanh::LeanObject,
    mut v_i_1866_: usize,
    mut v_stop_1867_: usize,
    mut v_b_1868_: u64,
) -> u64 {
    let mut v___y_1870_: u64 = 0;
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: usize = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u64 = 0;
    let mut v_hash_1878_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = lean_usize_dec_eq(v_i_1866_, v_stop_1867_);
                if v___x_1875_ == 0 {
                    v___x_1876_ = lean_array_uget_borrowed(v_as_1865_, v_i_1866_);
                    if crate::leanh::lean_obj_tag(v___x_1876_) == 0 {
                        v___x_1877_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0);
                        v___y_1870_ = v___x_1877_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1878_ = crate::leanh::lean_ctor_get_uint64(
                            v___x_1876_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1870_ = v_hash_1878_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1868_;
                }
            }
            1 => {
                v___x_1871_ = lean_uint64_mix_hash(v_b_1868_, v___y_1870_);
                v___x_1872_ = 1usize;
                v___x_1873_ = lean_usize_add(v_i_1866_, v___x_1872_);
                v_i_1866_ = v___x_1873_;
                v_b_1868_ = v___x_1871_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___boxed(
    mut v_as_1879_: *mut crate::leanh::LeanObject,
    mut v_i_1880_: *mut crate::leanh::LeanObject,
    mut v_stop_1881_: *mut crate::leanh::LeanObject,
    mut v_b_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1883_: usize = 0;
    let mut v_stop_boxed_1884_: usize = 0;
    let mut v_b_boxed_1885_: u64 = 0;
    let mut v_res_1886_: u64 = 0;
    let mut v_r_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1883_ = crate::leanh::lean_unbox_usize(v_i_1880_);
    crate::leanh::lean_dec(v_i_1880_);
    v_stop_boxed_1884_ = crate::leanh::lean_unbox_usize(v_stop_1881_);
    crate::leanh::lean_dec(v_stop_1881_);
    v_b_boxed_1885_ = crate::leanh::lean_unbox_uint64(v_b_1882_);
    crate::leanh::lean_dec_ref(v_b_1882_);
    v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_as_1879_, v_i_boxed_1883_, v_stop_boxed_1884_, v_b_boxed_1885_);
    crate::leanh::lean_dec_ref(v_as_1879_);
    v_r_1887_ = crate::leanh::lean_box_uint64(v_res_1886_);
    return v_r_1887_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_1888_: *mut crate::leanh::LeanObject,
    mut v_x_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1898_: u64 = 0;
    let mut v___x_1899_: u64 = 0;
    let mut v___x_1900_: u64 = 0;
    let mut v_fold_1901_: u64 = 0;
    let mut v___x_1902_: u64 = 0;
    let mut v___x_1903_: u64 = 0;
    let mut v___x_1904_: u64 = 0;
    let mut v___x_1905_: usize = 0;
    let mut v___x_1906_: usize = 0;
    let mut v___x_1907_: usize = 0;
    let mut v___x_1908_: usize = 0;
    let mut v___x_1909_: usize = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u64 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: usize = 0;
    let mut v___x_1923_: u64 = 0;
    let mut v___x_1924_: usize = 0;
    let mut v___x_1925_: usize = 0;
    let mut v___x_1926_: u64 = 0;
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1889_) == 0 {
                    return v_x_1888_;
                } else {
                    v_key_1890_ = crate::leanh::lean_ctor_get(v_x_1889_, 0);
                    v_value_1891_ = crate::leanh::lean_ctor_get(v_x_1889_, 1);
                    v_tail_1892_ = crate::leanh::lean_ctor_get(v_x_1889_, 2);
                    v_isSharedCheck_1927_ = (!crate::leanh::lean_is_exclusive(v_x_1889_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1894_ = v_x_1889_;
                        v_isShared_1895_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1892_);
                        crate::leanh::lean_inc(v_value_1891_);
                        crate::leanh::lean_inc(v_key_1890_);
                        crate::leanh::lean_dec(v_x_1889_);
                        v___x_1894_ = crate::leanh::lean_box(0);
                        v_isShared_1895_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1896_ = lean_array_get_size(v_x_1888_);
                v___x_1916_ = 7u64;
                v___x_1917_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1918_ = lean_array_get_size(v_key_1890_);
                v___x_1919_ = lean_nat_dec_lt(v___x_1917_, v___x_1918_);
                if v___x_1919_ == 0 {
                    v___y_1898_ = v___x_1916_;
                    state = 2;
                    continue;
                } else {
                    v___x_1920_ = lean_nat_dec_le(v___x_1918_, v___x_1918_);
                    if v___x_1920_ == 0 {
                        if v___x_1919_ == 0 {
                            v___y_1898_ = v___x_1916_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1921_ = 0usize;
                            v___x_1922_ = lean_usize_of_nat(v___x_1918_);
                            v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_key_1890_, v___x_1921_, v___x_1922_, v___x_1916_);
                            v___y_1898_ = v___x_1923_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1924_ = 0usize;
                        v___x_1925_ = lean_usize_of_nat(v___x_1918_);
                        v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_key_1890_, v___x_1924_, v___x_1925_, v___x_1916_);
                        v___y_1898_ = v___x_1926_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1899_ = 32u64;
                v___x_1900_ = lean_uint64_shift_right(v___y_1898_, v___x_1899_);
                v_fold_1901_ = lean_uint64_xor(v___y_1898_, v___x_1900_);
                v___x_1902_ = 16u64;
                v___x_1903_ = lean_uint64_shift_right(v_fold_1901_, v___x_1902_);
                v___x_1904_ = lean_uint64_xor(v_fold_1901_, v___x_1903_);
                v___x_1905_ = lean_uint64_to_usize(v___x_1904_);
                v___x_1906_ = lean_usize_of_nat(v___x_1896_);
                v___x_1907_ = 1usize;
                v___x_1908_ = lean_usize_sub(v___x_1906_, v___x_1907_);
                v___x_1909_ = lean_usize_land(v___x_1905_, v___x_1908_);
                v___x_1910_ = lean_array_uget_borrowed(v_x_1888_, v___x_1909_);
                crate::leanh::lean_inc(v___x_1910_);
                if v_isShared_1895_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1894_, 2, v___x_1910_);
                    v___x_1912_ = v___x_1894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_key_1890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_value_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___x_1910_);
                    v___x_1912_ = v_reuseFailAlloc_1915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1913_ = lean_array_uset(v_x_1888_, v___x_1909_, v___x_1912_);
                v_x_1888_ = v___x_1913_;
                v_x_1889_ = v_tail_1892_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3___redArg(
    mut v_i_1928_: *mut crate::leanh::LeanObject,
    mut v_source_1929_: *mut crate::leanh::LeanObject,
    mut v_target_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v_es_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = lean_array_get_size(v_source_1929_);
                v___x_1932_ = lean_nat_dec_lt(v_i_1928_, v___x_1931_);
                if v___x_1932_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1929_);
                    crate::leanh::lean_dec(v_i_1928_);
                    return v_target_1930_;
                } else {
                    v_es_1933_ = lean_array_fget(v_source_1929_, v_i_1928_);
                    v___x_1934_ = crate::leanh::lean_box(0);
                    v_source_1935_ = lean_array_fset(v_source_1929_, v_i_1928_, v___x_1934_);
                    v_target_1936_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1930_, v_es_1933_);
                    v___x_1937_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1938_ = lean_nat_add(v_i_1928_, v___x_1937_);
                    crate::leanh::lean_dec(v_i_1928_);
                    v_i_1928_ = v___x_1938_;
                    v_source_1929_ = v_source_1935_;
                    v_target_1930_ = v_target_1936_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1___redArg(
    mut v_data_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = lean_array_get_size(v_data_1940_);
    v___x_1942_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1943_ = lean_nat_mul(v___x_1941_, v___x_1942_);
    v___x_1944_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1945_ = crate::leanh::lean_box(0);
    v___x_1946_ = lean_mk_array(v_nbuckets_1943_, v___x_1945_);
    v___x_1947_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3___redArg(v___x_1944_, v_data_1940_, v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(
    mut v_xs_1948_: *mut crate::leanh::LeanObject,
    mut v_ys_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1952_: u8 = 0;
    let mut v_one_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1951_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1952_ = lean_nat_dec_eq(v_x_1950_, v_zero_1951_);
                if v_isZero_1952_ == 1 {
                    crate::leanh::lean_dec(v_x_1950_);
                    return v_isZero_1952_;
                } else {
                    v_one_1953_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1954_ = lean_nat_sub(v_x_1950_, v_one_1953_);
                    crate::leanh::lean_dec(v_x_1950_);
                    v___x_1955_ = lean_array_fget_borrowed(v_xs_1948_, v_n_1954_);
                    v___x_1956_ = lean_array_fget_borrowed(v_ys_1949_, v_n_1954_);
                    v___x_1957_ = lean_name_eq(v___x_1955_, v___x_1956_);
                    if v___x_1957_ == 0 {
                        crate::leanh::lean_dec(v_n_1954_);
                        return v___x_1957_;
                    } else {
                        v_x_1950_ = v_n_1954_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_xs_1959_: *mut crate::leanh::LeanObject,
    mut v_ys_1960_: *mut crate::leanh::LeanObject,
    mut v_x_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1962_: u8 = 0;
    let mut v_r_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(v_xs_1959_, v_ys_1960_, v_x_1961_);
    crate::leanh::lean_dec_ref(v_ys_1960_);
    crate::leanh::lean_dec_ref(v_xs_1959_);
    v_r_1963_ = crate::leanh::lean_box((v_res_1962_) as usize);
    return v_r_1963_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v_x_1965_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1966_: u8 = 0;
    let mut v_key_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1965_) == 0 {
                    v___x_1966_ = 0;
                    return v___x_1966_;
                } else {
                    v_key_1967_ = crate::leanh::lean_ctor_get(v_x_1965_, 0);
                    v_tail_1968_ = crate::leanh::lean_ctor_get(v_x_1965_, 2);
                    v___x_1969_ = lean_array_get_size(v_key_1967_);
                    v___x_1970_ = lean_array_get_size(v_a_1964_);
                    v___x_1971_ = lean_nat_dec_eq(v___x_1969_, v___x_1970_);
                    if v___x_1971_ == 0 {
                        v_x_1965_ = v_tail_1968_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1973_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(v_key_1967_, v_a_1964_, v___x_1969_);
                        if v___x_1973_ == 0 {
                            v_x_1965_ = v_tail_1968_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1973_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg___boxed(
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_x_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1977_: u8 = 0;
    let mut v_r_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(v_a_1975_, v_x_1976_);
    crate::leanh::lean_dec(v_x_1976_);
    crate::leanh::lean_dec_ref(v_a_1975_);
    v_r_1978_ = crate::leanh::lean_box((v_res_1977_) as usize);
    return v_r_1978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(
    mut v_m_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
    mut v_b_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: u64 = 0;
    let mut v___x_1987_: u64 = 0;
    let mut v___x_1988_: u64 = 0;
    let mut v_fold_1989_: u64 = 0;
    let mut v___x_1990_: u64 = 0;
    let mut v___x_1991_: u64 = 0;
    let mut v___x_1992_: u64 = 0;
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: usize = 0;
    let mut v___x_1997_: usize = 0;
    let mut v_bkt_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v_val_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_unused_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u64 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: usize = 0;
    let mut v___x_2029_: usize = 0;
    let mut v___x_2030_: u64 = 0;
    let mut v___x_2031_: usize = 0;
    let mut v___x_2032_: usize = 0;
    let mut v___x_2033_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1982_ = crate::leanh::lean_ctor_get(v_m_1979_, 0);
                v_buckets_1983_ = crate::leanh::lean_ctor_get(v_m_1979_, 1);
                v___x_1984_ = lean_array_get_size(v_buckets_1983_);
                v___x_2023_ = 7u64;
                v___x_2024_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2025_ = lean_array_get_size(v_a_1980_);
                v___x_2026_ = lean_nat_dec_lt(v___x_2024_, v___x_2025_);
                if v___x_2026_ == 0 {
                    v___y_1986_ = v___x_2023_;
                    state = 1;
                    continue;
                } else {
                    v___x_2027_ = lean_nat_dec_le(v___x_2025_, v___x_2025_);
                    if v___x_2027_ == 0 {
                        if v___x_2026_ == 0 {
                            v___y_1986_ = v___x_2023_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2028_ = 0usize;
                            v___x_2029_ = lean_usize_of_nat(v___x_2025_);
                            v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_a_1980_, v___x_2028_, v___x_2029_, v___x_2023_);
                            v___y_1986_ = v___x_2030_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2031_ = 0usize;
                        v___x_2032_ = lean_usize_of_nat(v___x_2025_);
                        v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_a_1980_, v___x_2031_, v___x_2032_, v___x_2023_);
                        v___y_1986_ = v___x_2033_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1987_ = 32u64;
                v___x_1988_ = lean_uint64_shift_right(v___y_1986_, v___x_1987_);
                v_fold_1989_ = lean_uint64_xor(v___y_1986_, v___x_1988_);
                v___x_1990_ = 16u64;
                v___x_1991_ = lean_uint64_shift_right(v_fold_1989_, v___x_1990_);
                v___x_1992_ = lean_uint64_xor(v_fold_1989_, v___x_1991_);
                v___x_1993_ = lean_uint64_to_usize(v___x_1992_);
                v___x_1994_ = lean_usize_of_nat(v___x_1984_);
                v___x_1995_ = 1usize;
                v___x_1996_ = lean_usize_sub(v___x_1994_, v___x_1995_);
                v___x_1997_ = lean_usize_land(v___x_1993_, v___x_1996_);
                v_bkt_1998_ = lean_array_uget_borrowed(v_buckets_1983_, v___x_1997_);
                v___x_1999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(v_a_1980_, v_bkt_1998_);
                if v___x_1999_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1983_);
                    crate::leanh::lean_inc(v_size_1982_);
                    v_isSharedCheck_2020_ = (!crate::leanh::lean_is_exclusive(v_m_1979_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v_unused_2021_ = crate::leanh::lean_ctor_get(v_m_1979_, 1);
                        crate::leanh::lean_dec(v_unused_2021_);
                        v_unused_2022_ = crate::leanh::lean_ctor_get(v_m_1979_, 0);
                        crate::leanh::lean_dec(v_unused_2022_);
                        v___x_2001_ = v_m_1979_;
                        v_isShared_2002_ = v_isSharedCheck_2020_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1979_);
                        v___x_2001_ = crate::leanh::lean_box(0);
                        v_isShared_2002_ = v_isSharedCheck_2020_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1981_);
                    crate::leanh::lean_dec_ref(v_a_1980_);
                    return v_m_1979_;
                }
            }
            2 => {
                v___x_2003_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2004_ = lean_nat_add(v_size_1982_, v___x_2003_);
                crate::leanh::lean_dec(v_size_1982_);
                crate::leanh::lean_inc(v_bkt_1998_);
                v___x_2005_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2005_, 0, v_a_1980_);
                crate::leanh::lean_ctor_set(v___x_2005_, 1, v_b_1981_);
                crate::leanh::lean_ctor_set(v___x_2005_, 2, v_bkt_1998_);
                v_buckets_x27_2006_ = lean_array_uset(v_buckets_1983_, v___x_1997_, v___x_2005_);
                v___x_2007_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2008_ = lean_nat_mul(v_size_x27_2004_, v___x_2007_);
                v___x_2009_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2010_ = lean_nat_div(v___x_2008_, v___x_2009_);
                crate::leanh::lean_dec(v___x_2008_);
                v___x_2011_ = lean_array_get_size(v_buckets_x27_2006_);
                v___x_2012_ = lean_nat_dec_le(v___x_2010_, v___x_2011_);
                crate::leanh::lean_dec(v___x_2010_);
                if v___x_2012_ == 0 {
                    v_val_2013_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1___redArg(v_buckets_x27_2006_);
                    if v_isShared_2002_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2001_, 1, v_val_2013_);
                        crate::leanh::lean_ctor_set(v___x_2001_, 0, v_size_x27_2004_);
                        v___x_2015_ = v___x_2001_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_size_x27_2004_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_val_2013_);
                        v___x_2015_ = v_reuseFailAlloc_2016_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2002_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2001_, 1, v_buckets_x27_2006_);
                        crate::leanh::lean_ctor_set(v___x_2001_, 0, v_size_x27_2004_);
                        v___x_2018_ = v___x_2001_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2019_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_size_x27_2004_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_buckets_x27_2006_);
                        v___x_2018_ = v_reuseFailAlloc_2019_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2015_;
            }
            4 => {
                return v___x_2018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = crate::leanh::lean_box(0);
    v___x_2035_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2036_ = lean_mk_array(v___x_2035_, v___x_2034_);
    return v___x_2036_;
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2037_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0);
    v___x_2038_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2039_, 0, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2039_, 1, v___x_2037_);
    return v___x_2039_;
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
    v___x_2043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1);
    v___x_2044_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    crate::leanh::lean_ctor_set(v___x_2044_, 1, v___x_2043_);
    crate::leanh::lean_ctor_set(v___x_2044_, 2, v___x_2042_);
    return v___x_2044_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1(
    mut v_x_2045_: *mut crate::leanh::LeanObject,
    mut v_x_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2046_) == 0 {
                    return v_x_2045_;
                } else {
                    v_head_2047_ = crate::leanh::lean_ctor_get(v_x_2046_, 0);
                    crate::leanh::lean_inc(v_head_2047_);
                    v_tail_2048_ = crate::leanh::lean_ctor_get(v_x_2046_, 1);
                    crate::leanh::lean_inc(v_tail_2048_);
                    crate::leanh::lean_dec_ref_known(v_x_2046_, 2);
                    v___x_2049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3);
                    v___x_2050_ = l_Lean_CollectLevelParams_visitLevel(v_head_2047_, v___x_2049_);
                    v_params_2051_ = crate::leanh::lean_ctor_get(v___x_2050_, 2);
                    crate::leanh::lean_inc_ref(v_params_2051_);
                    crate::leanh::lean_dec_ref(v___x_2050_);
                    v___x_2052_ = crate::leanh::lean_box(0);
                    v___x_2053_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(v_x_2045_, v_params_2051_, v___x_2052_);
                    v_x_2045_ = v___x_2053_;
                    v_x_2046_ = v_tail_2048_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(
    mut v_us_2055_: *mut crate::leanh::LeanObject,
    mut v_____r_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_st_ref_take(v___y_2057_);
    v___x_2060_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1(v___x_2059_, v_us_2055_);
    v___x_2061_ = lean_st_ref_set(v___y_2057_, v___x_2060_);
    v___x_2062_ = crate::leanh::lean_box(0);
    return v___x_2062_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0___boxed(
    mut v_us_2063_: *mut crate::leanh::LeanObject,
    mut v_____r_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
    mut v___y_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2067_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(
            v_us_2063_,
            v_____r_2064_,
            v___y_2065_,
        );
    crate::leanh::lean_dec(v___y_2065_);
    return v_res_2067_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0;
    v___x_2070_ = lean_string_utf8_byte_size(v___x_2069_);
    return v___x_2070_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1(
    mut v_nm_u2080_2071_: *mut crate::leanh::LeanObject,
    mut v_e_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2076_: u8 = 0;
    let mut v___y_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: u8 = 0;
    let mut v_pre_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: u8 = 0;
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2072_) {
                3 => {
                    v_u_2079_ = crate::leanh::lean_ctor_get(v_e_2072_, 0);
                    crate::leanh::lean_inc(v_u_2079_);
                    crate::leanh::lean_dec_ref_known(v_e_2072_, 1);
                    v___x_2080_ = lean_st_ref_take(v___y_2073_);
                    v___x_2081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3);
                    v___x_2082_ = l_Lean_CollectLevelParams_visitLevel(v_u_2079_, v___x_2081_);
                    v_params_2083_ = crate::leanh::lean_ctor_get(v___x_2082_, 2);
                    crate::leanh::lean_inc_ref(v_params_2083_);
                    crate::leanh::lean_dec_ref(v___x_2082_);
                    v___x_2084_ = crate::leanh::lean_box(0);
                    v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(v___x_2080_, v_params_2083_, v___x_2084_);
                    v___x_2086_ = lean_st_ref_set(v___y_2073_, v___x_2085_);
                    state = 1;
                    continue;
                }
                4 => {
                    v_declName_2087_ = crate::leanh::lean_ctor_get(v_e_2072_, 0);
                    crate::leanh::lean_inc(v_declName_2087_);
                    v_us_2088_ = crate::leanh::lean_ctor_get(v_e_2072_, 1);
                    crate::leanh::lean_inc(v_us_2088_);
                    crate::leanh::lean_dec_ref_known(v_e_2072_, 2);
                    if crate::leanh::lean_obj_tag(v_declName_2087_) == 1 {
                        v_pre_2094_ = crate::leanh::lean_ctor_get(v_declName_2087_, 0);
                        crate::leanh::lean_inc(v_pre_2094_);
                        v_str_2095_ = crate::leanh::lean_ctor_get(v_declName_2087_, 1);
                        crate::leanh::lean_inc_ref(v_str_2095_);
                        crate::leanh::lean_dec_ref_known(v_declName_2087_, 2);
                        v___x_2096_ = lean_name_eq(v_pre_2094_, v_nm_u2080_2071_);
                        crate::leanh::lean_dec(v_pre_2094_);
                        if v___x_2096_ == 0 {
                            crate::leanh::lean_dec_ref(v_str_2095_);
                            v___y_2093_ = v___x_2096_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2097_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0;
                            v___x_2098_ = lean_string_utf8_byte_size(v_str_2095_);
                            v___x_2099_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1);
                            v___x_2100_ = lean_nat_dec_le(v___x_2099_, v___x_2098_);
                            if v___x_2100_ == 0 {
                                crate::leanh::lean_dec_ref(v_str_2095_);
                                state = 3;
                                continue;
                            } else {
                                v___x_2101_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2102_ = lean_string_memcmp(
                                    v_str_2095_,
                                    v___x_2097_,
                                    v___x_2101_,
                                    v___x_2101_,
                                    v___x_2099_,
                                );
                                crate::leanh::lean_dec_ref(v_str_2095_);
                                v___y_2093_ = v___x_2102_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2087_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v___x_2104_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(v_us_2088_, v___x_2103_, v___y_2073_);
                        v___y_2078_ = v___x_2104_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_2072_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2076_ = 1;
                return v___x_2076_;
            }
            2 => {
                state = 1;
                continue;
            }
            3 => {
                v___x_2090_ = crate::leanh::lean_box(0);
                v___x_2091_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(v_us_2088_, v___x_2090_, v___y_2073_);
                v___y_2078_ = v___x_2091_;
                state = 2;
                continue;
            }
            4 => {
                if v___y_2093_ == 0 {
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_us_2088_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___boxed(
    mut v_nm_u2080_2105_: *mut crate::leanh::LeanObject,
    mut v_e_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2109_: u8 = 0;
    let mut v_r_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1(
            v_nm_u2080_2105_,
            v_e_2106_,
            v___y_2107_,
        );
    crate::leanh::lean_dec(v___y_2107_);
    crate::leanh::lean_dec(v_nm_u2080_2105_);
    v_r_2110_ = crate::leanh::lean_box((v_res_2109_) as usize);
    return v_r_2110_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_x_2112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2112_) == 0 {
                    v___x_2113_ = crate::leanh::lean_box(0);
                    return v___x_2113_;
                } else {
                    v_key_2114_ = crate::leanh::lean_ctor_get(v_x_2112_, 0);
                    v_value_2115_ = crate::leanh::lean_ctor_get(v_x_2112_, 1);
                    v_tail_2116_ = crate::leanh::lean_ctor_get(v_x_2112_, 2);
                    v___x_2117_ = lean_expr_eqv(v_key_2114_, v_a_2111_);
                    if v___x_2117_ == 0 {
                        v_x_2112_ = v_tail_2116_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2115_);
                        v___x_2119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2119_, 0, v_value_2115_);
                        return v___x_2119_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_x_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(v_a_2120_, v_x_2121_);
    crate::leanh::lean_dec(v_x_2121_);
    crate::leanh::lean_dec_ref(v_a_2120_);
    return v_res_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(
    mut v_m_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u64 = 0;
    let mut v___x_2128_: u64 = 0;
    let mut v___x_2129_: u64 = 0;
    let mut v_fold_2130_: u64 = 0;
    let mut v___x_2131_: u64 = 0;
    let mut v___x_2132_: u64 = 0;
    let mut v___x_2133_: u64 = 0;
    let mut v___x_2134_: usize = 0;
    let mut v___x_2135_: usize = 0;
    let mut v___x_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: usize = 0;
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2125_ = crate::leanh::lean_ctor_get(v_m_2123_, 1);
    v___x_2126_ = lean_array_get_size(v_buckets_2125_);
    v___x_2127_ = l_Lean_Expr_hash(v_a_2124_);
    v___x_2128_ = 32u64;
    v___x_2129_ = lean_uint64_shift_right(v___x_2127_, v___x_2128_);
    v_fold_2130_ = lean_uint64_xor(v___x_2127_, v___x_2129_);
    v___x_2131_ = 16u64;
    v___x_2132_ = lean_uint64_shift_right(v_fold_2130_, v___x_2131_);
    v___x_2133_ = lean_uint64_xor(v_fold_2130_, v___x_2132_);
    v___x_2134_ = lean_uint64_to_usize(v___x_2133_);
    v___x_2135_ = lean_usize_of_nat(v___x_2126_);
    v___x_2136_ = 1usize;
    v___x_2137_ = lean_usize_sub(v___x_2135_, v___x_2136_);
    v___x_2138_ = lean_usize_land(v___x_2134_, v___x_2137_);
    v___x_2139_ = lean_array_uget_borrowed(v_buckets_2125_, v___x_2138_);
    v___x_2140_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(v_a_2124_, v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg___boxed(
    mut v_m_2141_: *mut crate::leanh::LeanObject,
    mut v_a_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v_m_2141_, v_a_2142_);
    crate::leanh::lean_dec_ref(v_a_2142_);
    crate::leanh::lean_dec_ref(v_m_2141_);
    return v_res_2143_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(
    mut v_a_2144_: *mut crate::leanh::LeanObject,
    mut v_b_2145_: *mut crate::leanh::LeanObject,
    mut v_x_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2153_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2146_) == 0 {
                    crate::leanh::lean_dec(v_b_2145_);
                    crate::leanh::lean_dec_ref(v_a_2144_);
                    return v_x_2146_;
                } else {
                    v_key_2147_ = crate::leanh::lean_ctor_get(v_x_2146_, 0);
                    v_value_2148_ = crate::leanh::lean_ctor_get(v_x_2146_, 1);
                    v_tail_2149_ = crate::leanh::lean_ctor_get(v_x_2146_, 2);
                    v_isSharedCheck_2161_ = (!crate::leanh::lean_is_exclusive(v_x_2146_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2151_ = v_x_2146_;
                        v_isShared_2152_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2149_);
                        crate::leanh::lean_inc(v_value_2148_);
                        crate::leanh::lean_inc(v_key_2147_);
                        crate::leanh::lean_dec(v_x_2146_);
                        v___x_2151_ = crate::leanh::lean_box(0);
                        v_isShared_2152_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2153_ = lean_expr_eqv(v_key_2147_, v_a_2144_);
                if v___x_2153_ == 0 {
                    v___x_2154_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(v_a_2144_, v_b_2145_, v_tail_2149_);
                    if v_isShared_2152_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2151_, 2, v___x_2154_);
                        v___x_2156_ = v___x_2151_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2157_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_key_2147_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_value_2148_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 2, v___x_2154_);
                        v___x_2156_ = v_reuseFailAlloc_2157_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2148_);
                    crate::leanh::lean_dec(v_key_2147_);
                    if v_isShared_2152_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2151_, 1, v_b_2145_);
                        crate::leanh::lean_ctor_set(v___x_2151_, 0, v_a_2144_);
                        v___x_2159_ = v___x_2151_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2160_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2144_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_b_2145_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_tail_2149_);
                        v___x_2159_ = v_reuseFailAlloc_2160_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2156_;
            }
            3 => {
                return v___x_2159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14___redArg(
    mut v_x_2162_: *mut crate::leanh::LeanObject,
    mut v_x_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u64 = 0;
    let mut v___x_2172_: u64 = 0;
    let mut v___x_2173_: u64 = 0;
    let mut v_fold_2174_: u64 = 0;
    let mut v___x_2175_: u64 = 0;
    let mut v___x_2176_: u64 = 0;
    let mut v___x_2177_: u64 = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: usize = 0;
    let mut v___x_2181_: usize = 0;
    let mut v___x_2182_: usize = 0;
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2163_) == 0 {
                    return v_x_2162_;
                } else {
                    v_key_2164_ = crate::leanh::lean_ctor_get(v_x_2163_, 0);
                    v_value_2165_ = crate::leanh::lean_ctor_get(v_x_2163_, 1);
                    v_tail_2166_ = crate::leanh::lean_ctor_get(v_x_2163_, 2);
                    v_isSharedCheck_2189_ = (!crate::leanh::lean_is_exclusive(v_x_2163_)) as u8;
                    if v_isSharedCheck_2189_ == 0 {
                        v___x_2168_ = v_x_2163_;
                        v_isShared_2169_ = v_isSharedCheck_2189_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2166_);
                        crate::leanh::lean_inc(v_value_2165_);
                        crate::leanh::lean_inc(v_key_2164_);
                        crate::leanh::lean_dec(v_x_2163_);
                        v___x_2168_ = crate::leanh::lean_box(0);
                        v_isShared_2169_ = v_isSharedCheck_2189_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2170_ = lean_array_get_size(v_x_2162_);
                v___x_2171_ = l_Lean_Expr_hash(v_key_2164_);
                v___x_2172_ = 32u64;
                v___x_2173_ = lean_uint64_shift_right(v___x_2171_, v___x_2172_);
                v_fold_2174_ = lean_uint64_xor(v___x_2171_, v___x_2173_);
                v___x_2175_ = 16u64;
                v___x_2176_ = lean_uint64_shift_right(v_fold_2174_, v___x_2175_);
                v___x_2177_ = lean_uint64_xor(v_fold_2174_, v___x_2176_);
                v___x_2178_ = lean_uint64_to_usize(v___x_2177_);
                v___x_2179_ = lean_usize_of_nat(v___x_2170_);
                v___x_2180_ = 1usize;
                v___x_2181_ = lean_usize_sub(v___x_2179_, v___x_2180_);
                v___x_2182_ = lean_usize_land(v___x_2178_, v___x_2181_);
                v___x_2183_ = lean_array_uget_borrowed(v_x_2162_, v___x_2182_);
                crate::leanh::lean_inc(v___x_2183_);
                if v_isShared_2169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2168_, 2, v___x_2183_);
                    v___x_2185_ = v___x_2168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_key_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_value_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 2, v___x_2183_);
                    v___x_2185_ = v_reuseFailAlloc_2188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2186_ = lean_array_uset(v_x_2162_, v___x_2182_, v___x_2185_);
                v_x_2162_ = v___x_2186_;
                v_x_2163_ = v_tail_2166_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13___redArg(
    mut v_i_2190_: *mut crate::leanh::LeanObject,
    mut v_source_2191_: *mut crate::leanh::LeanObject,
    mut v_target_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v_es_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = lean_array_get_size(v_source_2191_);
                v___x_2194_ = lean_nat_dec_lt(v_i_2190_, v___x_2193_);
                if v___x_2194_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2191_);
                    crate::leanh::lean_dec(v_i_2190_);
                    return v_target_2192_;
                } else {
                    v_es_2195_ = lean_array_fget(v_source_2191_, v_i_2190_);
                    v___x_2196_ = crate::leanh::lean_box(0);
                    v_source_2197_ = lean_array_fset(v_source_2191_, v_i_2190_, v___x_2196_);
                    v_target_2198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14___redArg(v_target_2192_, v_es_2195_);
                    v___x_2199_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2200_ = lean_nat_add(v_i_2190_, v___x_2199_);
                    crate::leanh::lean_dec(v_i_2190_);
                    v_i_2190_ = v___x_2200_;
                    v_source_2191_ = v_source_2197_;
                    v_target_2192_ = v_target_2198_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11___redArg(
    mut v_data_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = lean_array_get_size(v_data_2202_);
    v___x_2204_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2205_ = lean_nat_mul(v___x_2203_, v___x_2204_);
    v___x_2206_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2207_ = crate::leanh::lean_box(0);
    v___x_2208_ = lean_mk_array(v_nbuckets_2205_, v___x_2207_);
    v___x_2209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13___redArg(v___x_2206_, v_data_2202_, v___x_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(
    mut v_a_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2212_: u8 = 0;
    let mut v_key_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2211_) == 0 {
                    v___x_2212_ = 0;
                    return v___x_2212_;
                } else {
                    v_key_2213_ = crate::leanh::lean_ctor_get(v_x_2211_, 0);
                    v_tail_2214_ = crate::leanh::lean_ctor_get(v_x_2211_, 2);
                    v___x_2215_ = lean_expr_eqv(v_key_2213_, v_a_2210_);
                    if v___x_2215_ == 0 {
                        v_x_2211_ = v_tail_2214_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2215_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg___boxed(
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_x_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2219_: u8 = 0;
    let mut v_r_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(v_a_2217_, v_x_2218_);
    crate::leanh::lean_dec(v_x_2218_);
    crate::leanh::lean_dec_ref(v_a_2217_);
    v_r_2220_ = crate::leanh::lean_box((v_res_2219_) as usize);
    return v_r_2220_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6___redArg(
    mut v_m_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_b_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: u64 = 0;
    let mut v___x_2231_: u64 = 0;
    let mut v___x_2232_: u64 = 0;
    let mut v_fold_2233_: u64 = 0;
    let mut v___x_2234_: u64 = 0;
    let mut v___x_2235_: u64 = 0;
    let mut v___x_2236_: u64 = 0;
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: usize = 0;
    let mut v___x_2240_: usize = 0;
    let mut v___x_2241_: usize = 0;
    let mut v_bkt_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v_val_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2224_ = crate::leanh::lean_ctor_get(v_m_2221_, 0);
                v_buckets_2225_ = crate::leanh::lean_ctor_get(v_m_2221_, 1);
                v_isSharedCheck_2268_ = (!crate::leanh::lean_is_exclusive(v_m_2221_)) as u8;
                if v_isSharedCheck_2268_ == 0 {
                    v___x_2227_ = v_m_2221_;
                    v_isShared_2228_ = v_isSharedCheck_2268_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2225_);
                    crate::leanh::lean_inc(v_size_2224_);
                    crate::leanh::lean_dec(v_m_2221_);
                    v___x_2227_ = crate::leanh::lean_box(0);
                    v_isShared_2228_ = v_isSharedCheck_2268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2229_ = lean_array_get_size(v_buckets_2225_);
                v___x_2230_ = l_Lean_Expr_hash(v_a_2222_);
                v___x_2231_ = 32u64;
                v___x_2232_ = lean_uint64_shift_right(v___x_2230_, v___x_2231_);
                v_fold_2233_ = lean_uint64_xor(v___x_2230_, v___x_2232_);
                v___x_2234_ = 16u64;
                v___x_2235_ = lean_uint64_shift_right(v_fold_2233_, v___x_2234_);
                v___x_2236_ = lean_uint64_xor(v_fold_2233_, v___x_2235_);
                v___x_2237_ = lean_uint64_to_usize(v___x_2236_);
                v___x_2238_ = lean_usize_of_nat(v___x_2229_);
                v___x_2239_ = 1usize;
                v___x_2240_ = lean_usize_sub(v___x_2238_, v___x_2239_);
                v___x_2241_ = lean_usize_land(v___x_2237_, v___x_2240_);
                v_bkt_2242_ = lean_array_uget_borrowed(v_buckets_2225_, v___x_2241_);
                v___x_2243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(v_a_2222_, v_bkt_2242_);
                if v___x_2243_ == 0 {
                    v___x_2244_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2245_ = lean_nat_add(v_size_2224_, v___x_2244_);
                    crate::leanh::lean_dec(v_size_2224_);
                    crate::leanh::lean_inc(v_bkt_2242_);
                    v___x_2246_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2246_, 0, v_a_2222_);
                    crate::leanh::lean_ctor_set(v___x_2246_, 1, v_b_2223_);
                    crate::leanh::lean_ctor_set(v___x_2246_, 2, v_bkt_2242_);
                    v_buckets_x27_2247_ =
                        lean_array_uset(v_buckets_2225_, v___x_2241_, v___x_2246_);
                    v___x_2248_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2249_ = lean_nat_mul(v_size_x27_2245_, v___x_2248_);
                    v___x_2250_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2251_ = lean_nat_div(v___x_2249_, v___x_2250_);
                    crate::leanh::lean_dec(v___x_2249_);
                    v___x_2252_ = lean_array_get_size(v_buckets_x27_2247_);
                    v___x_2253_ = lean_nat_dec_le(v___x_2251_, v___x_2252_);
                    crate::leanh::lean_dec(v___x_2251_);
                    if v___x_2253_ == 0 {
                        v_val_2254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11___redArg(v_buckets_x27_2247_);
                        if v_isShared_2228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2227_, 1, v_val_2254_);
                            crate::leanh::lean_ctor_set(v___x_2227_, 0, v_size_x27_2245_);
                            v___x_2256_ = v___x_2227_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2257_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2257_,
                                0,
                                v_size_x27_2245_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_val_2254_);
                            v___x_2256_ = v_reuseFailAlloc_2257_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2227_, 1, v_buckets_x27_2247_);
                            crate::leanh::lean_ctor_set(v___x_2227_, 0, v_size_x27_2245_);
                            v___x_2259_ = v___x_2227_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2260_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2260_,
                                0,
                                v_size_x27_2245_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2260_,
                                1,
                                v_buckets_x27_2247_,
                            );
                            v___x_2259_ = v_reuseFailAlloc_2260_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2242_);
                    v___x_2261_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2262_ =
                        lean_array_uset(v_buckets_2225_, v___x_2241_, v___x_2261_);
                    v___x_2263_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(v_a_2222_, v_b_2223_, v_bkt_2242_);
                    v___x_2264_ = lean_array_uset(v_buckets_x27_2262_, v___x_2241_, v___x_2263_);
                    if v_isShared_2228_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2227_, 1, v___x_2264_);
                        v___x_2266_ = v___x_2227_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_size_2224_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
                        v___x_2266_ = v_reuseFailAlloc_2267_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2256_;
            }
            3 => {
                return v___x_2259_;
            }
            4 => {
                return v___x_2266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(
    mut v_g_2269_: *mut crate::leanh::LeanObject,
    mut v_e_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2281_ = lean_st_ref_get(v_a_2271_);
                v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v___x_2281_, v_e_2270_);
                crate::leanh::lean_dec(v___x_2281_);
                if crate::leanh::lean_obj_tag(v___x_2282_) == 0 {
                    crate::leanh::lean_inc_ref(v_g_2269_);
                    crate::leanh::lean_inc(v___y_2272_);
                    crate::leanh::lean_inc_ref(v_e_2270_);
                    v___x_2283_ = crate::leanh::lean_apply_3(
                        v_g_2269_,
                        v_e_2270_,
                        v___y_2272_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_2290_ = (crate::leanh::lean_unbox(v___x_2283_) as u8);
                    if v___x_2290_ == 0 {
                        crate::leanh::lean_dec_ref(v_g_2269_);
                        v___x_2291_ = crate::leanh::lean_box(0);
                        v_val_2275_ = v___x_2291_;
                        state = 1;
                        continue;
                    } else {
                        match crate::leanh::lean_obj_tag(v_e_2270_) {
                            7 => {
                                v_binderType_2292_ = crate::leanh::lean_ctor_get(v_e_2270_, 1);
                                v_body_2293_ = crate::leanh::lean_ctor_get(v_e_2270_, 2);
                                crate::leanh::lean_inc_ref(v_body_2293_);
                                crate::leanh::lean_inc_ref(v_binderType_2292_);
                                v_d_2285_ = v_binderType_2292_;
                                v_b_2286_ = v_body_2293_;
                                v___y_2287_ = v_a_2271_;
                                state = 3;
                                continue;
                            }
                            6 => {
                                v_binderType_2294_ = crate::leanh::lean_ctor_get(v_e_2270_, 1);
                                v_body_2295_ = crate::leanh::lean_ctor_get(v_e_2270_, 2);
                                crate::leanh::lean_inc_ref(v_body_2295_);
                                crate::leanh::lean_inc_ref(v_binderType_2294_);
                                v_d_2285_ = v_binderType_2294_;
                                v_b_2286_ = v_body_2295_;
                                v___y_2287_ = v_a_2271_;
                                state = 3;
                                continue;
                            }
                            8 => {
                                v_type_2296_ = crate::leanh::lean_ctor_get(v_e_2270_, 1);
                                v_value_2297_ = crate::leanh::lean_ctor_get(v_e_2270_, 2);
                                v_body_2298_ = crate::leanh::lean_ctor_get(v_e_2270_, 3);
                                crate::leanh::lean_inc_ref(v_type_2296_);
                                crate::leanh::lean_inc_ref_n(v_g_2269_, 2);
                                v___x_2299_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_type_2296_, v_a_2271_, v___y_2272_);
                                crate::leanh::lean_inc_ref(v_value_2297_);
                                v___x_2300_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_value_2297_, v_a_2271_, v___y_2272_);
                                crate::leanh::lean_inc_ref(v_body_2298_);
                                v___x_2301_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_body_2298_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2301_;
                                state = 2;
                                continue;
                            }
                            5 => {
                                v_fn_2302_ = crate::leanh::lean_ctor_get(v_e_2270_, 0);
                                v_arg_2303_ = crate::leanh::lean_ctor_get(v_e_2270_, 1);
                                crate::leanh::lean_inc_ref(v_fn_2302_);
                                crate::leanh::lean_inc_ref(v_g_2269_);
                                v___x_2304_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_fn_2302_, v_a_2271_, v___y_2272_);
                                crate::leanh::lean_inc_ref(v_arg_2303_);
                                v___x_2305_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_arg_2303_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2305_;
                                state = 2;
                                continue;
                            }
                            10 => {
                                v_expr_2306_ = crate::leanh::lean_ctor_get(v_e_2270_, 1);
                                crate::leanh::lean_inc_ref(v_expr_2306_);
                                v___x_2307_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_expr_2306_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2307_;
                                state = 2;
                                continue;
                            }
                            11 => {
                                v_struct_2308_ = crate::leanh::lean_ctor_get(v_e_2270_, 2);
                                crate::leanh::lean_inc_ref(v_struct_2308_);
                                v___x_2309_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_struct_2308_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2309_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref(v_g_2269_);
                                v___x_2310_ = crate::leanh::lean_box(0);
                                v_val_2275_ = v___x_2310_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    crate::leanh::lean_dec_ref(v_g_2269_);
                    v_val_2311_ = crate::leanh::lean_ctor_get(v___x_2282_, 0);
                    crate::leanh::lean_inc(v_val_2311_);
                    crate::leanh::lean_dec_ref_known(v___x_2282_, 1);
                    return v_val_2311_;
                }
            }
            1 => {
                v___x_2276_ = lean_st_ref_take(v_a_2271_);
                v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6___redArg(v___x_2276_, v_e_2270_, v_val_2275_);
                v___x_2278_ = lean_st_ref_set(v_a_2271_, v___x_2277_);
                return v_val_2275_;
            }
            2 => {
                v_val_2275_ = v___y_2280_;
                state = 1;
                continue;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_g_2269_);
                v___x_2288_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_d_2285_, v___y_2287_, v___y_2272_);
                v___x_2289_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_b_2286_, v___y_2287_, v___y_2272_);
                v___y_2280_ = v___x_2289_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg___boxed(
    mut v_g_2312_: *mut crate::leanh::LeanObject,
    mut v_e_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2312_, v_e_2313_, v_a_2314_, v___y_2315_);
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec(v_a_2314_);
    return v_res_2317_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2318_ = crate::leanh::lean_box(0);
    v___x_2319_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2320_ = lean_mk_array(v___x_2319_, v___x_2318_);
    return v___x_2320_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0);
    v___x_2322_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2321_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2(
    mut v___f_2324_: *mut crate::leanh::LeanObject,
    mut v_e_2325_: *mut crate::leanh::LeanObject,
    mut v_x_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1);
    v___x_2329_ = lean_st_mk_ref(v___x_2328_);
    v___x_2330_ = lean_st_mk_ref(v___x_2328_);
    v___x_2331_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v___f_2324_, v_e_2325_, v___x_2330_, v___x_2329_);
    v___x_2332_ = lean_st_ref_get(v___x_2330_);
    crate::leanh::lean_dec(v___x_2330_);
    crate::leanh::lean_dec(v___x_2332_);
    v___x_2333_ = lean_st_ref_get(v___x_2329_);
    crate::leanh::lean_dec(v___x_2329_);
    return v___x_2333_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___boxed(
    mut v___f_2334_: *mut crate::leanh::LeanObject,
    mut v_e_2335_: *mut crate::leanh::LeanObject,
    mut v_x_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2(
            v___f_2334_,
            v_e_2335_,
            v_x_2336_,
        );
    return v_res_2338_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped(
    mut v_e_2339_: *mut crate::leanh::LeanObject,
    mut v_nm_u2080_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2341_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_2341_, 0, v_nm_u2080_2340_);
    v___f_2342_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___f_2342_, 0, v___f_2341_);
    crate::leanh::lean_closure_set(v___f_2342_, 1, v_e_2339_);
    v___x_2343_ = l_runST___redArg(v___f_2342_);
    return v___x_2343_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0(
    mut v_00_u03b2_2344_: *mut crate::leanh::LeanObject,
    mut v_m_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_b_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(v_m_2345_, v_a_2346_, v_b_2347_);
    return v___x_2348_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2(
    mut v_x_2349_: *mut crate::leanh::LeanObject,
    mut v_g_2350_: *mut crate::leanh::LeanObject,
    mut v_e_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2350_, v_e_2351_, v_a_2352_, v___y_2353_);
    return v___x_2355_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___boxed(
    mut v_x_2356_: *mut crate::leanh::LeanObject,
    mut v_g_2357_: *mut crate::leanh::LeanObject,
    mut v_e_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2(v_x_2356_, v_g_2357_, v_e_2358_, v_a_2359_, v___y_2360_);
    crate::leanh::lean_dec(v___y_2360_);
    crate::leanh::lean_dec(v_a_2359_);
    return v_res_2362_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0(
    mut v_00_u03b2_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_x_2365_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2366_: u8 = 0;
    v___x_2366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(v_a_2364_, v_x_2365_);
    return v___x_2366_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___boxed(
    mut v_00_u03b2_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_x_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2370_: u8 = 0;
    let mut v_r_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0(v_00_u03b2_2367_, v_a_2368_, v_x_2369_);
    crate::leanh::lean_dec(v_x_2369_);
    crate::leanh::lean_dec_ref(v_a_2368_);
    v_r_2371_ = crate::leanh::lean_box((v_res_2370_) as usize);
    return v_r_2371_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1(
    mut v_00_u03b2_2372_: *mut crate::leanh::LeanObject,
    mut v_data_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1___redArg(v_data_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5(
    mut v_00_u03b2_2375_: *mut crate::leanh::LeanObject,
    mut v_m_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v_m_2376_, v_a_2377_);
    return v___x_2378_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___boxed(
    mut v_00_u03b2_2379_: *mut crate::leanh::LeanObject,
    mut v_m_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5(v_00_u03b2_2379_, v_m_2380_, v_a_2381_);
    crate::leanh::lean_dec_ref(v_a_2381_);
    crate::leanh::lean_dec_ref(v_m_2380_);
    return v_res_2382_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6(
    mut v_00_u03b2_2383_: *mut crate::leanh::LeanObject,
    mut v_m_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_b_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6___redArg(v_m_2384_, v_a_2385_, v_b_2386_);
    return v___x_2387_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1(
    mut v_xs_2388_: *mut crate::leanh::LeanObject,
    mut v_ys_2389_: *mut crate::leanh::LeanObject,
    mut v_hsz_2390_: *mut crate::leanh::LeanObject,
    mut v_x_2391_: *mut crate::leanh::LeanObject,
    mut v_x_2392_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2393_: u8 = 0;
    v___x_2393_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(v_xs_2388_, v_ys_2389_, v_x_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2394_: *mut crate::leanh::LeanObject,
    mut v_ys_2395_: *mut crate::leanh::LeanObject,
    mut v_hsz_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
    mut v_x_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2399_: u8 = 0;
    let mut v_r_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1(v_xs_2394_, v_ys_2395_, v_hsz_2396_, v_x_2397_, v_x_2398_);
    crate::leanh::lean_dec_ref(v_ys_2395_);
    crate::leanh::lean_dec_ref(v_xs_2394_);
    v_r_2400_ = crate::leanh::lean_box((v_res_2399_) as usize);
    return v_r_2400_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2401_: *mut crate::leanh::LeanObject,
    mut v_i_2402_: *mut crate::leanh::LeanObject,
    mut v_source_2403_: *mut crate::leanh::LeanObject,
    mut v_target_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3___redArg(v_i_2402_, v_source_2403_, v_target_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8(
    mut v_00_u03b2_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
    mut v_x_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(v_a_2407_, v_x_2408_);
    return v___x_2409_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b2_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
    mut v_x_2412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8(v_00_u03b2_2410_, v_a_2411_, v_x_2412_);
    crate::leanh::lean_dec(v_x_2412_);
    crate::leanh::lean_dec_ref(v_a_2411_);
    return v_res_2413_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10(
    mut v_00_u03b2_2414_: *mut crate::leanh::LeanObject,
    mut v_a_2415_: *mut crate::leanh::LeanObject,
    mut v_x_2416_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2417_: u8 = 0;
    v___x_2417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(v_a_2415_, v_x_2416_);
    return v___x_2417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___boxed(
    mut v_00_u03b2_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_x_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2421_: u8 = 0;
    let mut v_r_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10(v_00_u03b2_2418_, v_a_2419_, v_x_2420_);
    crate::leanh::lean_dec(v_x_2420_);
    crate::leanh::lean_dec_ref(v_a_2419_);
    v_r_2422_ = crate::leanh::lean_box((v_res_2421_) as usize);
    return v_r_2422_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11(
    mut v_00_u03b2_2423_: *mut crate::leanh::LeanObject,
    mut v_data_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11___redArg(v_data_2424_);
    return v___x_2425_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12(
    mut v_00_u03b2_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_b_2428_: *mut crate::leanh::LeanObject,
    mut v_x_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(v_a_2427_, v_b_2428_, v_x_2429_);
    return v___x_2430_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_2431_: *mut crate::leanh::LeanObject,
    mut v_x_2432_: *mut crate::leanh::LeanObject,
    mut v_x_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2432_, v_x_2433_);
    return v___x_2434_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13(
    mut v_00_u03b2_2435_: *mut crate::leanh::LeanObject,
    mut v_i_2436_: *mut crate::leanh::LeanObject,
    mut v_source_2437_: *mut crate::leanh::LeanObject,
    mut v_target_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13___redArg(v_i_2436_, v_source_2437_, v_target_2438_);
    return v___x_2439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14(
    mut v_00_u03b2_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
    mut v_x_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14___redArg(v_x_2441_, v_x_2442_);
    return v___x_2443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0(
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_as_2445_: *mut crate::leanh::LeanObject,
    mut v_i_2446_: usize,
    mut v_stop_2447_: usize,
) -> u8 {
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: usize = 0;
    let mut v___x_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2448_ = lean_usize_dec_eq(v_i_2446_, v_stop_2447_);
                if v___x_2448_ == 0 {
                    v___x_2449_ = lean_array_uget_borrowed(v_as_2445_, v_i_2446_);
                    v___x_2450_ = lean_name_eq(v_a_2444_, v___x_2449_);
                    if v___x_2450_ == 0 {
                        v___x_2451_ = 1usize;
                        v___x_2452_ = lean_usize_add(v_i_2446_, v___x_2451_);
                        v_i_2446_ = v___x_2452_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2450_;
                    }
                } else {
                    v___x_2454_ = 0;
                    return v___x_2454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0___boxed(
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_as_2456_: *mut crate::leanh::LeanObject,
    mut v_i_2457_: *mut crate::leanh::LeanObject,
    mut v_stop_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2459_: usize = 0;
    let mut v_stop_boxed_2460_: usize = 0;
    let mut v_res_2461_: u8 = 0;
    let mut v_r_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2459_ = crate::leanh::lean_unbox_usize(v_i_2457_);
    crate::leanh::lean_dec(v_i_2457_);
    v_stop_boxed_2460_ = crate::leanh::lean_unbox_usize(v_stop_2458_);
    crate::leanh::lean_dec(v_stop_2458_);
    v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0(v_a_2455_, v_as_2456_, v_i_boxed_2459_, v_stop_boxed_2460_);
    crate::leanh::lean_dec_ref(v_as_2456_);
    crate::leanh::lean_dec(v_a_2455_);
    v_r_2462_ = crate::leanh::lean_box((v_res_2461_) as usize);
    return v_r_2462_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(
    mut v_as_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    v___x_2465_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2466_ = lean_array_get_size(v_as_2463_);
    v___x_2467_ = lean_nat_dec_lt(v___x_2465_, v___x_2466_);
    if v___x_2467_ == 0 {
        return v___x_2467_;
    } else {
        if v___x_2467_ == 0 {
            return v___x_2467_;
        } else {
            let mut v___x_2468_: usize = 0;
            let mut v___x_2469_: usize = 0;
            let mut v___x_2470_: u8 = 0;
            v___x_2468_ = 0usize;
            v___x_2469_ = lean_usize_of_nat(v___x_2466_);
            v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0(v_a_2464_, v_as_2463_, v___x_2468_, v___x_2469_);
            return v___x_2470_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0___boxed(
    mut v_as_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: u8 = 0;
    let mut v_r_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_as_2471_, v_a_2472_);
    crate::leanh::lean_dec(v_a_2472_);
    crate::leanh::lean_dec_ref(v_as_2471_);
    v_r_2474_ = crate::leanh::lean_box((v_res_2473_) as usize);
    return v_r_2474_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(
    mut v_goodLevels_2475_: *mut crate::leanh::LeanObject,
    mut v_as_2476_: *mut crate::leanh::LeanObject,
    mut v_i_2477_: usize,
    mut v_stop_2478_: usize,
    mut v_b_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: usize = 0;
    let mut v___x_2483_: usize = 0;
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: u8 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2485_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
                if v___x_2485_ == 0 {
                    v___x_2486_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
                    v___x_2487_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_goodLevels_2475_, v___x_2486_);
                    if v___x_2487_ == 0 {
                        crate::leanh::lean_inc(v___x_2486_);
                        v___x_2488_ = lean_array_push(v_b_2479_, v___x_2486_);
                        v___y_2481_ = v___x_2488_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2481_ = v_b_2479_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2479_;
                }
            }
            1 => {
                v___x_2482_ = 1usize;
                v___x_2483_ = lean_usize_add(v_i_2477_, v___x_2482_);
                v_i_2477_ = v___x_2483_;
                v_b_2479_ = v___y_2481_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2___boxed(
    mut v_goodLevels_2489_: *mut crate::leanh::LeanObject,
    mut v_as_2490_: *mut crate::leanh::LeanObject,
    mut v_i_2491_: *mut crate::leanh::LeanObject,
    mut v_stop_2492_: *mut crate::leanh::LeanObject,
    mut v_b_2493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2494_: usize = 0;
    let mut v_stop_boxed_2495_: usize = 0;
    let mut v_res_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2494_ = crate::leanh::lean_unbox_usize(v_i_2491_);
    crate::leanh::lean_dec(v_i_2491_);
    v_stop_boxed_2495_ = crate::leanh::lean_unbox_usize(v_stop_2492_);
    crate::leanh::lean_dec(v_stop_2492_);
    v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2489_, v_as_2490_, v_i_boxed_2494_, v_stop_boxed_2495_, v_b_2493_);
    crate::leanh::lean_dec_ref(v_as_2490_);
    crate::leanh::lean_dec_ref(v_goodLevels_2489_);
    return v_res_2496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(
    mut v_goodLevels_2497_: *mut crate::leanh::LeanObject,
    mut v_sz_2498_: usize,
    mut v_i_2499_: usize,
    mut v_bs_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: usize = 0;
    let mut v___x_2508_: usize = 0;
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: usize = 0;
    let mut v___x_2516_: usize = 0;
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: usize = 0;
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_usize_dec_lt(v_i_2499_, v_sz_2498_);
                if v___x_2501_ == 0 {
                    return v_bs_2500_;
                } else {
                    v___x_2502_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_v_2503_ = lean_array_uget(v_bs_2500_, v_i_2499_);
                    v_bs_x27_2504_ = lean_array_uset(v_bs_2500_, v_i_2499_, v___x_2502_);
                    v___x_2511_ = lean_array_get_size(v_v_2503_);
                    v___x_2512_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
                    v___x_2513_ = lean_nat_dec_lt(v___x_2502_, v___x_2511_);
                    if v___x_2513_ == 0 {
                        crate::leanh::lean_dec(v_v_2503_);
                        v___y_2506_ = v___x_2512_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2514_ = lean_nat_dec_le(v___x_2511_, v___x_2511_);
                        if v___x_2514_ == 0 {
                            if v___x_2513_ == 0 {
                                crate::leanh::lean_dec(v_v_2503_);
                                v___y_2506_ = v___x_2512_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2515_ = 0usize;
                                v___x_2516_ = lean_usize_of_nat(v___x_2511_);
                                v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2497_, v_v_2503_, v___x_2515_, v___x_2516_, v___x_2512_);
                                crate::leanh::lean_dec(v_v_2503_);
                                v___y_2506_ = v___x_2517_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2518_ = 0usize;
                            v___x_2519_ = lean_usize_of_nat(v___x_2511_);
                            v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2497_, v_v_2503_, v___x_2518_, v___x_2519_, v___x_2512_);
                            crate::leanh::lean_dec(v_v_2503_);
                            v___y_2506_ = v___x_2520_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2507_ = 1usize;
                v___x_2508_ = lean_usize_add(v_i_2499_, v___x_2507_);
                v___x_2509_ = lean_array_uset(v_bs_x27_2504_, v_i_2499_, v___y_2506_);
                v_i_2499_ = v___x_2508_;
                v_bs_2500_ = v___x_2509_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3___boxed(
    mut v_goodLevels_2521_: *mut crate::leanh::LeanObject,
    mut v_sz_2522_: *mut crate::leanh::LeanObject,
    mut v_i_2523_: *mut crate::leanh::LeanObject,
    mut v_bs_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2525_: usize = 0;
    let mut v_i_boxed_2526_: usize = 0;
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2525_ = crate::leanh::lean_unbox_usize(v_sz_2522_);
    crate::leanh::lean_dec(v_sz_2522_);
    v_i_boxed_2526_ = crate::leanh::lean_unbox_usize(v_i_2523_);
    crate::leanh::lean_dec(v_i_2523_);
    v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(v_goodLevels_2521_, v_sz_boxed_2525_, v_i_boxed_2526_, v_bs_2524_);
    crate::leanh::lean_dec_ref(v_goodLevels_2521_);
    return v_res_2527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(
    mut v_as_2528_: *mut crate::leanh::LeanObject,
    mut v_i_2529_: usize,
    mut v_stop_2530_: usize,
    mut v_b_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2532_ = lean_usize_dec_eq(v_i_2529_, v_stop_2530_);
                if v___x_2532_ == 0 {
                    v___x_2533_ = lean_array_uget_borrowed(v_as_2528_, v_i_2529_);
                    v___x_2534_ = l_Array_append___redArg(v_b_2531_, v___x_2533_);
                    v___x_2535_ = 1usize;
                    v___x_2536_ = lean_usize_add(v_i_2529_, v___x_2535_);
                    v_i_2529_ = v___x_2536_;
                    v_b_2531_ = v___x_2534_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2531_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5___boxed(
    mut v_as_2538_: *mut crate::leanh::LeanObject,
    mut v_i_2539_: *mut crate::leanh::LeanObject,
    mut v_stop_2540_: *mut crate::leanh::LeanObject,
    mut v_b_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2542_: usize = 0;
    let mut v_stop_boxed_2543_: usize = 0;
    let mut v_res_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2542_ = crate::leanh::lean_unbox_usize(v_i_2539_);
    crate::leanh::lean_dec(v_i_2539_);
    v_stop_boxed_2543_ = crate::leanh::lean_unbox_usize(v_stop_2540_);
    crate::leanh::lean_dec(v_stop_2540_);
    v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_as_2538_, v_i_boxed_2542_, v_stop_boxed_2543_, v_b_2541_);
    crate::leanh::lean_dec_ref(v_as_2538_);
    return v_res_2544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(
    mut v_as_2545_: *mut crate::leanh::LeanObject,
    mut v_i_2546_: usize,
    mut v_stop_2547_: usize,
    mut v_b_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: usize = 0;
    let mut v___x_2552_: usize = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2554_ = lean_usize_dec_eq(v_i_2546_, v_stop_2547_);
                if v___x_2554_ == 0 {
                    v___x_2555_ = lean_array_uget_borrowed(v_as_2545_, v_i_2546_);
                    v___x_2556_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_b_2548_, v___x_2555_);
                    if v___x_2556_ == 0 {
                        crate::leanh::lean_inc(v___x_2555_);
                        v___x_2557_ = lean_array_push(v_b_2548_, v___x_2555_);
                        v___y_2550_ = v___x_2557_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2550_ = v_b_2548_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2548_;
                }
            }
            1 => {
                v___x_2551_ = 1usize;
                v___x_2552_ = lean_usize_add(v_i_2546_, v___x_2551_);
                v_i_2546_ = v___x_2552_;
                v_b_2548_ = v___y_2550_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4___boxed(
    mut v_as_2558_: *mut crate::leanh::LeanObject,
    mut v_i_2559_: *mut crate::leanh::LeanObject,
    mut v_stop_2560_: *mut crate::leanh::LeanObject,
    mut v_b_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2562_: usize = 0;
    let mut v_stop_boxed_2563_: usize = 0;
    let mut v_res_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2562_ = crate::leanh::lean_unbox_usize(v_i_2559_);
    crate::leanh::lean_dec(v_i_2559_);
    v_stop_boxed_2563_ = crate::leanh::lean_unbox_usize(v_stop_2560_);
    crate::leanh::lean_dec(v_stop_2560_);
    v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v_as_2558_, v_i_boxed_2562_, v_stop_boxed_2563_, v_b_2561_);
    crate::leanh::lean_dec_ref(v_as_2558_);
    return v_res_2564_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(
    mut v_as_2565_: *mut crate::leanh::LeanObject,
    mut v_i_2566_: usize,
    mut v_stop_2567_: usize,
    mut v_b_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: u8 = 0;
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2574_ = lean_usize_dec_eq(v_i_2566_, v_stop_2567_);
                if v___x_2574_ == 0 {
                    v___x_2575_ = lean_array_uget_borrowed(v_as_2565_, v_i_2566_);
                    v___x_2576_ = lean_array_get_size(v___x_2575_);
                    v___x_2577_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2578_ = lean_nat_dec_eq(v___x_2576_, v___x_2577_);
                    if v___x_2578_ == 0 {
                        v___y_2570_ = v_b_2568_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2579_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2580_ = lean_array_fget_borrowed(v___x_2575_, v___x_2579_);
                        crate::leanh::lean_inc(v___x_2580_);
                        v___x_2581_ = lean_array_push(v_b_2568_, v___x_2580_);
                        v___y_2570_ = v___x_2581_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2568_;
                }
            }
            1 => {
                v___x_2571_ = 1usize;
                v___x_2572_ = lean_usize_add(v_i_2566_, v___x_2571_);
                v_i_2566_ = v___x_2572_;
                v_b_2568_ = v___y_2570_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2___boxed(
    mut v_as_2582_: *mut crate::leanh::LeanObject,
    mut v_i_2583_: *mut crate::leanh::LeanObject,
    mut v_stop_2584_: *mut crate::leanh::LeanObject,
    mut v_b_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2586_: usize = 0;
    let mut v_stop_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2586_ = crate::leanh::lean_unbox_usize(v_i_2583_);
    crate::leanh::lean_dec(v_i_2583_);
    v_stop_boxed_2587_ = crate::leanh::lean_unbox_usize(v_stop_2584_);
    crate::leanh::lean_dec(v_stop_2584_);
    v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2582_, v_i_boxed_2586_, v_stop_boxed_2587_, v_b_2585_);
    crate::leanh::lean_dec_ref(v_as_2582_);
    return v_res_2588_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(
    mut v_as_2589_: *mut crate::leanh::LeanObject,
    mut v_start_2590_: *mut crate::leanh::LeanObject,
    mut v_stop_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    v___x_2592_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
    v___x_2593_ = lean_nat_dec_lt(v_start_2590_, v_stop_2591_);
    if v___x_2593_ == 0 {
        return v___x_2592_;
    } else {
        let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2595_: u8 = 0;
        v___x_2594_ = lean_array_get_size(v_as_2589_);
        v___x_2595_ = lean_nat_dec_le(v_stop_2591_, v___x_2594_);
        if v___x_2595_ == 0 {
            let mut v___x_2596_: u8 = 0;
            v___x_2596_ = lean_nat_dec_lt(v_start_2590_, v___x_2594_);
            if v___x_2596_ == 0 {
                return v___x_2592_;
            } else {
                let mut v___x_2597_: usize = 0;
                let mut v___x_2598_: usize = 0;
                let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2597_ = lean_usize_of_nat(v_start_2590_);
                v___x_2598_ = lean_usize_of_nat(v___x_2594_);
                v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2589_, v___x_2597_, v___x_2598_, v___x_2592_);
                return v___x_2599_;
            }
        } else {
            let mut v___x_2600_: usize = 0;
            let mut v___x_2601_: usize = 0;
            let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2600_ = lean_usize_of_nat(v_start_2590_);
            v___x_2601_ = lean_usize_of_nat(v_stop_2591_);
            v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2589_, v___x_2600_, v___x_2601_, v___x_2592_);
            return v___x_2602_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1___boxed(
    mut v_as_2603_: *mut crate::leanh::LeanObject,
    mut v_start_2604_: *mut crate::leanh::LeanObject,
    mut v_stop_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(v_as_2603_, v_start_2604_, v_stop_2605_);
    crate::leanh::lean_dec(v_stop_2605_);
    crate::leanh::lean_dec(v_start_2604_);
    crate::leanh::lean_dec_ref(v_as_2603_);
    return v_res_2606_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams(
    mut v_l_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goodLevels_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v_sz_2615_: usize = 0;
    let mut v___x_2616_: usize = 0;
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: usize = 0;
    let mut v___x_2626_: usize = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: usize = 0;
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: usize = 0;
    let mut v___x_2635_: usize = 0;
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: usize = 0;
    let mut v___x_2638_: usize = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2611_ = lean_array_get_size(v_l_2609_);
                v_goodLevels_2612_ = l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(v_l_2609_, v___x_2610_, v___x_2611_);
                v___x_2613_ = lean_array_get_size(v_goodLevels_2612_);
                v___x_2614_ = lean_nat_dec_eq(v___x_2613_, v___x_2610_);
                if v___x_2614_ == 0 {
                    v_sz_2615_ = lean_array_size(v_l_2609_);
                    v___x_2616_ = 0usize;
                    v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(v_goodLevels_2612_, v_sz_2615_, v___x_2616_, v_l_2609_);
                    crate::leanh::lean_dec_ref(v_goodLevels_2612_);
                    v_l_2609_ = v___x_2617_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_goodLevels_2612_);
                    v___x_2619_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
                    v___x_2631_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0;
                    v___x_2632_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
                    if v___x_2632_ == 0 {
                        crate::leanh::lean_dec_ref(v_l_2609_);
                        v___y_2621_ = v___x_2631_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2633_ = lean_nat_dec_le(v___x_2611_, v___x_2611_);
                        if v___x_2633_ == 0 {
                            if v___x_2632_ == 0 {
                                crate::leanh::lean_dec_ref(v_l_2609_);
                                v___y_2621_ = v___x_2631_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2634_ = 0usize;
                                v___x_2635_ = lean_usize_of_nat(v___x_2611_);
                                v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_l_2609_, v___x_2634_, v___x_2635_, v___x_2631_);
                                crate::leanh::lean_dec_ref(v_l_2609_);
                                v___y_2621_ = v___x_2636_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2637_ = 0usize;
                            v___x_2638_ = lean_usize_of_nat(v___x_2611_);
                            v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_l_2609_, v___x_2637_, v___x_2638_, v___x_2631_);
                            crate::leanh::lean_dec_ref(v_l_2609_);
                            v___y_2621_ = v___x_2639_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2622_ = lean_array_get_size(v___y_2621_);
                v___x_2623_ = lean_nat_dec_lt(v___x_2610_, v___x_2622_);
                if v___x_2623_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2621_);
                    return v___x_2619_;
                } else {
                    v___x_2624_ = lean_nat_dec_le(v___x_2622_, v___x_2622_);
                    if v___x_2624_ == 0 {
                        if v___x_2623_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2621_);
                            return v___x_2619_;
                        } else {
                            v___x_2625_ = 0usize;
                            v___x_2626_ = lean_usize_of_nat(v___x_2622_);
                            v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v___y_2621_, v___x_2625_, v___x_2626_, v___x_2619_);
                            crate::leanh::lean_dec_ref(v___y_2621_);
                            return v___x_2627_;
                        }
                    } else {
                        v___x_2628_ = 0usize;
                        v___x_2629_ = lean_usize_of_nat(v___x_2622_);
                        v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v___y_2621_, v___x_2628_, v___x_2629_, v___x_2619_);
                        crate::leanh::lean_dec_ref(v___y_2621_);
                        return v___x_2630_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
    mut v___y_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = lean_st_ref_get(v___y_2640_);
    v_infoState_2643_ = crate::leanh::lean_ctor_get(v___x_2642_, 8);
    crate::leanh::lean_inc_ref(v_infoState_2643_);
    crate::leanh::lean_dec(v___x_2642_);
    v_trees_2644_ = crate::leanh::lean_ctor_get(v_infoState_2643_, 2);
    crate::leanh::lean_inc_ref(v_trees_2644_);
    crate::leanh::lean_dec_ref(v_infoState_2643_);
    v___x_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2645_, 0, v_trees_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg___boxed(
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
            v___y_2646_,
        );
    crate::leanh::lean_dec(v___y_2646_);
    return v_res_2648_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1(
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
            v___y_2650_,
        );
    return v___x_2652_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___boxed(
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1(
        v___y_2653_,
        v___y_2654_,
    );
    crate::leanh::lean_dec(v___y_2654_);
    crate::leanh::lean_dec_ref(v___y_2653_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(
    mut v_o_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2660_ = lean_st_ref_get(v___y_2658_);
    v_env_2661_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
    crate::leanh::lean_inc_ref(v_env_2661_);
    crate::leanh::lean_dec(v___x_2660_);
    v___x_2662_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2663_ = crate::leanh::lean_ctor_get(v___x_2662_, 0);
    v_asyncMode_2664_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2663_, 2);
    v___x_2665_ = crate::leanh::lean_box(1);
    v___x_2666_ = crate::leanh::lean_box(0);
    v_linterSets_2667_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2665_,
        v___x_2662_,
        v_env_2661_,
        v_asyncMode_2664_,
        v___x_2666_,
    );
    v___x_2668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2668_, 0, v_o_2657_);
    crate::leanh::lean_ctor_set(v___x_2668_, 1, v_linterSets_2667_);
    v___x_2669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2669_, 0, v___x_2668_);
    return v___x_2669_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg___boxed(
    mut v_o_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_o_2670_, v___y_2671_);
    crate::leanh::lean_dec(v___y_2671_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = lean_st_ref_get(v___y_2675_);
    v_scopes_2678_ = crate::leanh::lean_ctor_get(v___x_2677_, 2);
    crate::leanh::lean_inc(v_scopes_2678_);
    crate::leanh::lean_dec(v___x_2677_);
    v___x_2679_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2680_ = l_List_head_x21___redArg(v___x_2679_, v_scopes_2678_);
    crate::leanh::lean_dec(v_scopes_2678_);
    v_opts_2681_ = crate::leanh::lean_ctor_get(v___x_2680_, 1);
    crate::leanh::lean_inc_ref(v_opts_2681_);
    crate::leanh::lean_dec(v___x_2680_);
    v___x_2682_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_opts_2681_, v___y_2675_);
    return v___x_2682_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0___boxed(
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2686_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(
            v___y_2683_,
            v___y_2684_,
        );
    crate::leanh::lean_dec(v___y_2684_);
    crate::leanh::lean_dec_ref(v___y_2683_);
    return v_res_2686_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0);
    v___x_2689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2689_, 0, v___x_2688_);
    return v___x_2689_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1);
    v___x_2691_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2692_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2692_, 0, v___x_2691_);
    crate::leanh::lean_ctor_set(v___x_2692_, 1, v___x_2691_);
    crate::leanh::lean_ctor_set(v___x_2692_, 2, v___x_2691_);
    crate::leanh::lean_ctor_set(v___x_2692_, 3, v___x_2691_);
    crate::leanh::lean_ctor_set(v___x_2692_, 4, v___x_2690_);
    crate::leanh::lean_ctor_set(v___x_2692_, 5, v___x_2690_);
    crate::leanh::lean_ctor_set(v___x_2692_, 6, v___x_2690_);
    crate::leanh::lean_ctor_set(v___x_2692_, 7, v___x_2690_);
    crate::leanh::lean_ctor_set(v___x_2692_, 8, v___x_2690_);
    crate::leanh::lean_ctor_set(v___x_2692_, 9, v___x_2690_);
    return v___x_2692_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2694_ = lean_mk_empty_array_with_capacity(v___x_2693_);
    v___x_2695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
    return v___x_2695_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = 5usize;
    v___x_2697_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2698_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2698_);
    v___x_2700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3);
    v___x_2701_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2701_, 0, v___x_2700_);
    crate::leanh::lean_ctor_set(v___x_2701_, 1, v___x_2699_);
    crate::leanh::lean_ctor_set(v___x_2701_, 2, v___x_2697_);
    crate::leanh::lean_ctor_set(v___x_2701_, 3, v___x_2697_);
    crate::leanh::lean_ctor_set_usize(v___x_2701_, 4, v___x_2696_);
    return v___x_2701_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = crate::leanh::lean_box(1);
    v___x_2703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4);
    v___x_2704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1);
    v___x_2705_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2705_, 0, v___x_2704_);
    crate::leanh::lean_ctor_set(v___x_2705_, 1, v___x_2703_);
    crate::leanh::lean_ctor_set(v___x_2705_, 2, v___x_2702_);
    return v___x_2705_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(
    mut v_msgData_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ = lean_st_ref_get(v___y_2707_);
    v_env_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
    crate::leanh::lean_inc_ref(v_env_2710_);
    crate::leanh::lean_dec(v___x_2709_);
    v___x_2711_ = lean_st_ref_get(v___y_2707_);
    v_scopes_2712_ = crate::leanh::lean_ctor_get(v___x_2711_, 2);
    crate::leanh::lean_inc(v_scopes_2712_);
    crate::leanh::lean_dec(v___x_2711_);
    v___x_2713_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2714_ = l_List_head_x21___redArg(v___x_2713_, v_scopes_2712_);
    crate::leanh::lean_dec(v_scopes_2712_);
    v_opts_2715_ = crate::leanh::lean_ctor_get(v___x_2714_, 1);
    crate::leanh::lean_inc_ref(v_opts_2715_);
    crate::leanh::lean_dec(v___x_2714_);
    v___x_2716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2);
    v___x_2717_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5);
    v___x_2718_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2718_, 0, v_env_2710_);
    crate::leanh::lean_ctor_set(v___x_2718_, 1, v___x_2716_);
    crate::leanh::lean_ctor_set(v___x_2718_, 2, v___x_2717_);
    crate::leanh::lean_ctor_set(v___x_2718_, 3, v_opts_2715_);
    v___x_2719_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2719_, 0, v___x_2718_);
    crate::leanh::lean_ctor_set(v___x_2719_, 1, v_msgData_2706_);
    v___x_2720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2720_, 0, v___x_2719_);
    return v___x_2720_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___boxed(
    mut v_msgData_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v_msgData_2721_, v___y_2722_);
    crate::leanh::lean_dec(v___y_2722_);
    return v_res_2724_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0(
    mut v___y_2726_: u8,
    mut v_suppressElabErrors_2727_: u8,
    mut v_x_2728_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2728_) == 1 {
        let mut v_pre_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2729_ = crate::leanh::lean_ctor_get(v_x_2728_, 0);
        if crate::leanh::lean_obj_tag(v_pre_2729_) == 0 {
            let mut v_str_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2732_: u8 = 0;
            v_str_2730_ = crate::leanh::lean_ctor_get(v_x_2728_, 1);
            v___x_2731_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0;
            v___x_2732_ = lean_string_dec_eq(v_str_2730_, v___x_2731_);
            if v___x_2732_ == 0 {
                return v___y_2726_;
            } else {
                return v_suppressElabErrors_2727_;
            }
        } else {
            return v___y_2726_;
        }
    } else {
        return v___y_2726_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___boxed(
    mut v___y_2733_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2734_: *mut crate::leanh::LeanObject,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_10221__boxed_2736_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2737_: u8 = 0;
    let mut v_res_2738_: u8 = 0;
    let mut v_r_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_10221__boxed_2736_ = (crate::leanh::lean_unbox(v___y_2733_) as u8);
    v_suppressElabErrors_boxed_2737_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2734_) as u8);
    v_res_2738_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0(v___y_10221__boxed_2736_, v_suppressElabErrors_boxed_2737_, v_x_2735_);
    crate::leanh::lean_dec(v_x_2735_);
    v_r_2739_ = crate::leanh::lean_box((v_res_2738_) as usize);
    return v_r_2739_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(
    mut v_opts_2740_: *mut crate::leanh::LeanObject,
    mut v_opt_2741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2742_ = crate::leanh::lean_ctor_get(v_opt_2741_, 0);
    v_defValue_2743_ = crate::leanh::lean_ctor_get(v_opt_2741_, 1);
    v_map_2744_ = crate::leanh::lean_ctor_get(v_opts_2740_, 0);
    v___x_2745_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2744_,
            v_name_2742_,
        );
    if crate::leanh::lean_obj_tag(v___x_2745_) == 0 {
        let mut v___x_2746_: u8 = 0;
        v___x_2746_ = (crate::leanh::lean_unbox(v_defValue_2743_) as u8);
        return v___x_2746_;
    } else {
        let mut v_val_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2747_ = crate::leanh::lean_ctor_get(v___x_2745_, 0);
        crate::leanh::lean_inc(v_val_2747_);
        crate::leanh::lean_dec_ref_known(v___x_2745_, 1);
        if crate::leanh::lean_obj_tag(v_val_2747_) == 1 {
            let mut v_v_2748_: u8 = 0;
            v_v_2748_ = crate::leanh::lean_ctor_get_uint8(v_val_2747_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2747_, 0);
            return v_v_2748_;
        } else {
            let mut v___x_2749_: u8 = 0;
            crate::leanh::lean_dec(v_val_2747_);
            v___x_2749_ = (crate::leanh::lean_unbox(v_defValue_2743_) as u8);
            return v___x_2749_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14___boxed(
    mut v_opts_2750_: *mut crate::leanh::LeanObject,
    mut v_opt_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2752_: u8 = 0;
    let mut v_r_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2752_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(v_opts_2750_, v_opt_2751_);
    crate::leanh::lean_dec_ref(v_opt_2751_);
    crate::leanh::lean_dec_ref(v_opts_2750_);
    v_r_2753_ = crate::leanh::lean_box((v_res_2752_) as usize);
    return v_r_2753_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(
    mut v_ref_2755_: *mut crate::leanh::LeanObject,
    mut v_msgData_2756_: *mut crate::leanh::LeanObject,
    mut v_severity_2757_: u8,
    mut v_isSilent_2758_: u8,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: u8 = 0;
    let mut v___y_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v_a_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2824_: u8 = 0;
    let mut v___y_2826_: u8 = 0;
    let mut v___y_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: u8 = 0;
    let mut v___y_2829_: u8 = 0;
    let mut v___y_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2833_: u8 = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v___y_2854_: u8 = 0;
    let mut v___y_2855_: u8 = 0;
    let mut v___y_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2857_: u8 = 0;
    let mut v___y_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: u8 = 0;
    let mut v___y_2863_: u8 = 0;
    let mut v___y_2864_: u8 = 0;
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___y_2881_: u8 = 0;
    let mut v___y_2882_: u8 = 0;
    let mut v___y_2883_: u8 = 0;
    let mut v___y_2885_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2879_ = 2;
                v___x_2897_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2757_, v___x_2879_);
                if v___x_2897_ == 0 {
                    v___y_2885_ = v___x_2897_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2756_);
                    v___x_2898_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2756_);
                    v___y_2885_ = v___x_2898_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2771_ = l_Lean_Elab_Command_getScope___redArg(v___y_2770_);
                if crate::leanh::lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                    crate::leanh::lean_inc(v_a_2772_);
                    crate::leanh::lean_dec_ref_known(v___x_2771_, 1);
                    v___x_2773_ = l_Lean_Elab_Command_getScope___redArg(v___y_2770_);
                    if crate::leanh::lean_obj_tag(v___x_2773_) == 0 {
                        v_a_2774_ = crate::leanh::lean_ctor_get(v___x_2773_, 0);
                        v_isSharedCheck_2808_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2773_)) as u8;
                        if v_isSharedCheck_2808_ == 0 {
                            v___x_2776_ = v___x_2773_;
                            v_isShared_2777_ = v_isSharedCheck_2808_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2774_);
                            crate::leanh::lean_dec(v___x_2773_);
                            v___x_2776_ = crate::leanh::lean_box(0);
                            v_isShared_2777_ = v_isSharedCheck_2808_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2772_);
                        crate::leanh::lean_dec_ref(v___y_2767_);
                        crate::leanh::lean_dec(v___y_2766_);
                        crate::leanh::lean_dec_ref(v___y_2764_);
                        v_a_2809_ = crate::leanh::lean_ctor_get(v___x_2773_, 0);
                        v_isSharedCheck_2816_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2773_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v___x_2811_ = v___x_2773_;
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2809_);
                            crate::leanh::lean_dec(v___x_2773_);
                            v___x_2811_ = crate::leanh::lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2767_);
                    crate::leanh::lean_dec(v___y_2766_);
                    crate::leanh::lean_dec_ref(v___y_2764_);
                    v_a_2817_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2824_ = (!crate::leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2824_ == 0 {
                        v___x_2819_ = v___x_2771_;
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2817_);
                        crate::leanh::lean_dec(v___x_2771_);
                        v___x_2819_ = crate::leanh::lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2778_ = lean_st_ref_take(v___y_2770_);
                v_currNamespace_2779_ = crate::leanh::lean_ctor_get(v_a_2772_, 2);
                crate::leanh::lean_inc(v_currNamespace_2779_);
                crate::leanh::lean_dec(v_a_2772_);
                v_openDecls_2780_ = crate::leanh::lean_ctor_get(v_a_2774_, 3);
                crate::leanh::lean_inc(v_openDecls_2780_);
                crate::leanh::lean_dec(v_a_2774_);
                v_env_2781_ = crate::leanh::lean_ctor_get(v___x_2778_, 0);
                v_messages_2782_ = crate::leanh::lean_ctor_get(v___x_2778_, 1);
                v_scopes_2783_ = crate::leanh::lean_ctor_get(v___x_2778_, 2);
                v_usedQuotCtxts_2784_ = crate::leanh::lean_ctor_get(v___x_2778_, 3);
                v_nextMacroScope_2785_ = crate::leanh::lean_ctor_get(v___x_2778_, 4);
                v_maxRecDepth_2786_ = crate::leanh::lean_ctor_get(v___x_2778_, 5);
                v_ngen_2787_ = crate::leanh::lean_ctor_get(v___x_2778_, 6);
                v_auxDeclNGen_2788_ = crate::leanh::lean_ctor_get(v___x_2778_, 7);
                v_infoState_2789_ = crate::leanh::lean_ctor_get(v___x_2778_, 8);
                v_traceState_2790_ = crate::leanh::lean_ctor_get(v___x_2778_, 9);
                v_snapshotTasks_2791_ = crate::leanh::lean_ctor_get(v___x_2778_, 10);
                v_isSharedCheck_2807_ = (!crate::leanh::lean_is_exclusive(v___x_2778_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2793_ = v___x_2778_;
                    v_isShared_2794_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2791_);
                    crate::leanh::lean_inc(v_traceState_2790_);
                    crate::leanh::lean_inc(v_infoState_2789_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2788_);
                    crate::leanh::lean_inc(v_ngen_2787_);
                    crate::leanh::lean_inc(v_maxRecDepth_2786_);
                    crate::leanh::lean_inc(v_nextMacroScope_2785_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2784_);
                    crate::leanh::lean_inc(v_scopes_2783_);
                    crate::leanh::lean_inc(v_messages_2782_);
                    crate::leanh::lean_inc(v_env_2781_);
                    crate::leanh::lean_dec(v___x_2778_);
                    v___x_2793_ = crate::leanh::lean_box(0);
                    v_isShared_2794_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2795_, 0, v_currNamespace_2779_);
                crate::leanh::lean_ctor_set(v___x_2795_, 1, v_openDecls_2780_);
                v___x_2796_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2796_, 1, v___y_2767_);
                crate::leanh::lean_inc_ref(v___y_2769_);
                crate::leanh::lean_inc_ref(v___y_2765_);
                v___x_2797_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2797_, 0, v___y_2765_);
                crate::leanh::lean_ctor_set(v___x_2797_, 1, v___y_2764_);
                crate::leanh::lean_ctor_set(v___x_2797_, 2, v___y_2766_);
                crate::leanh::lean_ctor_set(v___x_2797_, 3, v___y_2769_);
                crate::leanh::lean_ctor_set(v___x_2797_, 4, v___x_2796_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2763_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2768_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2758_,
                );
                v___x_2798_ = l_Lean_MessageLog_add(v___x_2797_, v_messages_2782_);
                if v_isShared_2794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2793_, 1, v___x_2798_);
                    v___x_2800_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_env_2781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_scopes_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_usedQuotCtxts_2784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_nextMacroScope_2785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 5, v_maxRecDepth_2786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 6, v_ngen_2787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 7, v_auxDeclNGen_2788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 8, v_infoState_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 9, v_traceState_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 10, v_snapshotTasks_2791_);
                    v___x_2800_ = v_reuseFailAlloc_2806_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2801_ = lean_st_ref_set(v___y_2770_, v___x_2800_);
                v___x_2802_ = crate::leanh::lean_box(0);
                if v_isShared_2777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2802_);
                    v___x_2804_ = v___x_2776_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2804_;
            }
            6 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2814_;
            }
            8 => {
                if v_isShared_2820_ == 0 {
                    v___x_2822_ = v___x_2819_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
                    v___x_2822_ = v_reuseFailAlloc_2823_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2822_;
            }
            10 => {
                v_fileName_2831_ = crate::leanh::lean_ctor_get(v___y_2759_, 0);
                v_fileMap_2832_ = crate::leanh::lean_ctor_get(v___y_2759_, 1);
                v_suppressElabErrors_2833_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2759_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_2834_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2756_,
                    );
                v___x_2835_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v___x_2834_, v___y_2760_);
                v_a_2836_ = crate::leanh::lean_ctor_get(v___x_2835_, 0);
                v_isSharedCheck_2852_ = (!crate::leanh::lean_is_exclusive(v___x_2835_)) as u8;
                if v_isSharedCheck_2852_ == 0 {
                    v___x_2838_ = v___x_2835_;
                    v_isShared_2839_ = v_isSharedCheck_2852_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2836_);
                    crate::leanh::lean_dec(v___x_2835_);
                    v___x_2838_ = crate::leanh::lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2852_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_2832_, 2);
                v___x_2840_ = l_Lean_FileMap_toPosition(v_fileMap_2832_, v___y_2827_);
                crate::leanh::lean_dec(v___y_2827_);
                v___x_2841_ = l_Lean_FileMap_toPosition(v_fileMap_2832_, v___y_2830_);
                crate::leanh::lean_dec(v___y_2830_);
                v___x_2842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                v___x_2843_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0;
                if v_suppressElabErrors_2833_ == 0 {
                    crate::leanh::lean_del_object(v___x_2838_);
                    v___y_2763_ = v___y_2828_;
                    v___y_2764_ = v___x_2840_;
                    v___y_2765_ = v_fileName_2831_;
                    v___y_2766_ = v___x_2842_;
                    v___y_2767_ = v_a_2836_;
                    v___y_2768_ = v___y_2829_;
                    v___y_2769_ = v___x_2843_;
                    v___y_2770_ = v___y_2760_;
                    state = 1;
                    continue;
                } else {
                    v___x_2844_ = crate::leanh::lean_box((v___y_2826_) as usize);
                    v___x_2845_ = crate::leanh::lean_box((v_suppressElabErrors_2833_) as usize);
                    v___f_2846_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2846_, 0, v___x_2844_);
                    crate::leanh::lean_closure_set(v___f_2846_, 1, v___x_2845_);
                    crate::leanh::lean_inc(v_a_2836_);
                    v___x_2847_ = l_Lean_MessageData_hasTag(v___f_2846_, v_a_2836_);
                    if v___x_2847_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2842_, 1);
                        crate::leanh::lean_dec_ref(v___x_2840_);
                        crate::leanh::lean_dec(v_a_2836_);
                        v___x_2848_ = crate::leanh::lean_box(0);
                        if v_isShared_2839_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2838_, 0, v___x_2848_);
                            v___x_2850_ = v___x_2838_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2851_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
                            v___x_2850_ = v_reuseFailAlloc_2851_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2838_);
                        v___y_2763_ = v___y_2828_;
                        v___y_2764_ = v___x_2840_;
                        v___y_2765_ = v_fileName_2831_;
                        v___y_2766_ = v___x_2842_;
                        v___y_2767_ = v_a_2836_;
                        v___y_2768_ = v___y_2829_;
                        v___y_2769_ = v___x_2843_;
                        v___y_2770_ = v___y_2760_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_2850_;
            }
            13 => {
                v___x_2859_ = l_Lean_Syntax_getTailPos_x3f(v___y_2856_, v___y_2855_);
                crate::leanh::lean_dec(v___y_2856_);
                if crate::leanh::lean_obj_tag(v___x_2859_) == 0 {
                    crate::leanh::lean_inc(v___y_2858_);
                    v___y_2826_ = v___y_2854_;
                    v___y_2827_ = v___y_2858_;
                    v___y_2828_ = v___y_2855_;
                    v___y_2829_ = v___y_2857_;
                    v___y_2830_ = v___y_2858_;
                    state = 10;
                    continue;
                } else {
                    v_val_2860_ = crate::leanh::lean_ctor_get(v___x_2859_, 0);
                    crate::leanh::lean_inc(v_val_2860_);
                    crate::leanh::lean_dec_ref_known(v___x_2859_, 1);
                    v___y_2826_ = v___y_2854_;
                    v___y_2827_ = v___y_2858_;
                    v___y_2828_ = v___y_2855_;
                    v___y_2829_ = v___y_2857_;
                    v___y_2830_ = v_val_2860_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_2865_ = l_Lean_Elab_Command_getRef___redArg(v___y_2759_);
                if crate::leanh::lean_obj_tag(v___x_2865_) == 0 {
                    v_a_2866_ = crate::leanh::lean_ctor_get(v___x_2865_, 0);
                    crate::leanh::lean_inc(v_a_2866_);
                    crate::leanh::lean_dec_ref_known(v___x_2865_, 1);
                    v_ref_2867_ = l_Lean_replaceRef(v_ref_2755_, v_a_2866_);
                    crate::leanh::lean_dec(v_a_2866_);
                    v___x_2868_ = l_Lean_Syntax_getPos_x3f(v_ref_2867_, v___y_2863_);
                    if crate::leanh::lean_obj_tag(v___x_2868_) == 0 {
                        v___x_2869_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_2854_ = v___y_2862_;
                        v___y_2855_ = v___y_2863_;
                        v___y_2856_ = v_ref_2867_;
                        v___y_2857_ = v___y_2864_;
                        v___y_2858_ = v___x_2869_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2870_ = crate::leanh::lean_ctor_get(v___x_2868_, 0);
                        crate::leanh::lean_inc(v_val_2870_);
                        crate::leanh::lean_dec_ref_known(v___x_2868_, 1);
                        v___y_2854_ = v___y_2862_;
                        v___y_2855_ = v___y_2863_;
                        v___y_2856_ = v_ref_2867_;
                        v___y_2857_ = v___y_2864_;
                        v___y_2858_ = v_val_2870_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2756_);
                    v_a_2871_ = crate::leanh::lean_ctor_get(v___x_2865_, 0);
                    v_isSharedCheck_2878_ = (!crate::leanh::lean_is_exclusive(v___x_2865_)) as u8;
                    if v_isSharedCheck_2878_ == 0 {
                        v___x_2873_ = v___x_2865_;
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2871_);
                        crate::leanh::lean_dec(v___x_2865_);
                        v___x_2873_ = crate::leanh::lean_box(0);
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2876_;
            }
            17 => {
                if v___y_2883_ == 0 {
                    v___y_2862_ = v___y_2881_;
                    v___y_2863_ = v___y_2882_;
                    v___y_2864_ = v_severity_2757_;
                    state = 14;
                    continue;
                } else {
                    v___y_2862_ = v___y_2881_;
                    v___y_2863_ = v___y_2882_;
                    v___y_2864_ = v___x_2879_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_2885_ == 0 {
                    v___x_2886_ = lean_st_ref_get(v___y_2760_);
                    v_scopes_2887_ = crate::leanh::lean_ctor_get(v___x_2886_, 2);
                    crate::leanh::lean_inc(v_scopes_2887_);
                    crate::leanh::lean_dec(v___x_2886_);
                    v___x_2888_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2889_ = l_List_head_x21___redArg(v___x_2888_, v_scopes_2887_);
                    crate::leanh::lean_dec(v_scopes_2887_);
                    v_opts_2890_ = crate::leanh::lean_ctor_get(v___x_2889_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2890_);
                    crate::leanh::lean_dec(v___x_2889_);
                    v___x_2891_ = 1;
                    v___x_2892_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2757_, v___x_2891_);
                    if v___x_2892_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2890_);
                        v___y_2881_ = v___y_2885_;
                        v___y_2882_ = v___y_2885_;
                        v___y_2883_ = v___x_2892_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2893_ = l_Lean_warningAsError;
                        v___x_2894_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(v_opts_2890_, v___x_2893_);
                        crate::leanh::lean_dec_ref(v_opts_2890_);
                        v___y_2881_ = v___y_2885_;
                        v___y_2882_ = v___y_2885_;
                        v___y_2883_ = v___x_2894_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2756_);
                    v___x_2895_ = crate::leanh::lean_box(0);
                    v___x_2896_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                    return v___x_2896_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___boxed(
    mut v_ref_2899_: *mut crate::leanh::LeanObject,
    mut v_msgData_2900_: *mut crate::leanh::LeanObject,
    mut v_severity_2901_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2906_: u8 = 0;
    let mut v_isSilent_boxed_2907_: u8 = 0;
    let mut v_res_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2906_ = (crate::leanh::lean_unbox(v_severity_2901_) as u8);
    v_isSilent_boxed_2907_ = (crate::leanh::lean_unbox(v_isSilent_2902_) as u8);
    v_res_2908_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(v_ref_2899_, v_msgData_2900_, v_severity_boxed_2906_, v_isSilent_boxed_2907_, v___y_2903_, v___y_2904_);
    crate::leanh::lean_dec(v___y_2904_);
    crate::leanh::lean_dec_ref(v___y_2903_);
    crate::leanh::lean_dec(v_ref_2899_);
    return v_res_2908_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(
    mut v_ref_2909_: *mut crate::leanh::LeanObject,
    mut v_msgData_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = 1;
    v___x_2915_ = 0;
    v___x_2916_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(v_ref_2909_, v_msgData_2910_, v___x_2914_, v___x_2915_, v___y_2911_, v___y_2912_);
    return v___x_2916_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5___boxed(
    mut v_ref_2917_: *mut crate::leanh::LeanObject,
    mut v_msgData_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2922_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(v_ref_2917_, v_msgData_2918_, v___y_2919_, v___y_2920_);
    crate::leanh::lean_dec(v___y_2920_);
    crate::leanh::lean_dec_ref(v___y_2919_);
    crate::leanh::lean_dec(v_ref_2917_);
    return v_res_2922_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0;
    v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
    return v___x_2925_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2;
    v___x_2928_ = l_Lean_stringToMessageData(v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4(
    mut v_linterOption_2929_: *mut crate::leanh::LeanObject,
    mut v_stx_2930_: *mut crate::leanh::LeanObject,
    mut v_msg_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_unused_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2935_ = crate::leanh::lean_ctor_get(v_linterOption_2929_, 0);
                v_isSharedCheck_2952_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_2929_)) as u8;
                if v_isSharedCheck_2952_ == 0 {
                    v_unused_2953_ = crate::leanh::lean_ctor_get(v_linterOption_2929_, 1);
                    crate::leanh::lean_dec(v_unused_2953_);
                    v___x_2937_ = v_linterOption_2929_;
                    v_isShared_2938_ = v_isSharedCheck_2952_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_2935_);
                    crate::leanh::lean_dec(v_linterOption_2929_);
                    v___x_2937_ = crate::leanh::lean_box(0);
                    v_isShared_2938_ = v_isSharedCheck_2952_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2939_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1);
                crate::leanh::lean_inc(v_name_2935_);
                v___x_2940_ = l_Lean_MessageData_ofName(v_name_2935_);
                if v_isShared_2938_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2937_, 7);
                    crate::leanh::lean_ctor_set(v___x_2937_, 1, v___x_2940_);
                    crate::leanh::lean_ctor_set(v___x_2937_, 0, v___x_2939_);
                    v___x_2942_ = v___x_2937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2940_);
                    v___x_2942_ = v_reuseFailAlloc_2951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2943_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3);
                v___x_2944_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2944_, 0, v___x_2942_);
                crate::leanh::lean_ctor_set(v___x_2944_, 1, v___x_2943_);
                v_disable_2945_ = l_Lean_MessageData_note(v___x_2944_);
                v___x_2946_ = l_Lean_Linter_linterMessageTag;
                v___x_2947_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2947_, 0, v_msg_2931_);
                crate::leanh::lean_ctor_set(v___x_2947_, 1, v_disable_2945_);
                v___x_2948_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2948_, 0, v___x_2946_);
                crate::leanh::lean_ctor_set(v___x_2948_, 1, v___x_2947_);
                v___x_2949_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2949_, 0, v_name_2935_);
                crate::leanh::lean_ctor_set(v___x_2949_, 1, v___x_2948_);
                v___x_2950_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(v_stx_2930_, v___x_2949_, v___y_2932_, v___y_2933_);
                return v___x_2950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___boxed(
    mut v_linterOption_2954_: *mut crate::leanh::LeanObject,
    mut v_stx_2955_: *mut crate::leanh::LeanObject,
    mut v_msg_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4(v_linterOption_2954_, v_stx_2955_, v_msg_2956_, v___y_2957_, v___y_2958_);
    crate::leanh::lean_dec(v___y_2958_);
    crate::leanh::lean_dec_ref(v___y_2957_);
    crate::leanh::lean_dec(v_stx_2955_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(
    mut v_linterOption_2961_: *mut crate::leanh::LeanObject,
    mut v_stx_2962_: *mut crate::leanh::LeanObject,
    mut v_msg_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2971_: u8 = 0;
    let mut v___x_2972_: u8 = 0;
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2967_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(v___y_2964_, v___y_2965_);
                v_a_2968_ = crate::leanh::lean_ctor_get(v___x_2967_, 0);
                v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v___x_2967_)) as u8;
                if v_isSharedCheck_2978_ == 0 {
                    v___x_2970_ = v___x_2967_;
                    v_isShared_2971_ = v_isSharedCheck_2978_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2968_);
                    crate::leanh::lean_dec(v___x_2967_);
                    v___x_2970_ = crate::leanh::lean_box(0);
                    v_isShared_2971_ = v_isSharedCheck_2978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2972_ = l_Lean_Linter_getLinterValue(v_linterOption_2961_, v_a_2968_);
                crate::leanh::lean_dec(v_a_2968_);
                if v___x_2972_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_2963_);
                    crate::leanh::lean_dec_ref(v_linterOption_2961_);
                    v___x_2973_ = crate::leanh::lean_box(0);
                    if v_isShared_2971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2970_, 0, v___x_2973_);
                        v___x_2975_ = v___x_2970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
                        v___x_2975_ = v_reuseFailAlloc_2976_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2970_);
                    v___x_2977_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4(v_linterOption_2961_, v_stx_2962_, v_msg_2963_, v___y_2964_, v___y_2965_);
                    return v___x_2977_;
                }
            }
            2 => {
                return v___x_2975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3___boxed(
    mut v_linterOption_2979_: *mut crate::leanh::LeanObject,
    mut v_stx_2980_: *mut crate::leanh::LeanObject,
    mut v_msg_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2985_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(
        v_linterOption_2979_,
        v_stx_2980_,
        v_msg_2981_,
        v___y_2982_,
        v___y_2983_,
    );
    crate::leanh::lean_dec(v___y_2983_);
    crate::leanh::lean_dec_ref(v___y_2982_);
    crate::leanh::lean_dec(v_stx_2980_);
    return v_res_2985_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ =
        l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0;
    v___x_2988_ = l_Lean_stringToMessageData(v___x_2987_);
    return v___x_2988_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2(
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2989_) == 0 {
                    v___x_2991_ = l_List_reverse___redArg(v_a_2990_);
                    return v___x_2991_;
                } else {
                    v_head_2992_ = crate::leanh::lean_ctor_get(v_a_2989_, 0);
                    v_tail_2993_ = crate::leanh::lean_ctor_get(v_a_2989_, 1);
                    v_isSharedCheck_3005_ = (!crate::leanh::lean_is_exclusive(v_a_2989_)) as u8;
                    if v_isSharedCheck_3005_ == 0 {
                        v___x_2995_ = v_a_2989_;
                        v_isShared_2996_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2993_);
                        crate::leanh::lean_inc(v_head_2992_);
                        crate::leanh::lean_dec(v_a_2989_);
                        v___x_2995_ = crate::leanh::lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1);
                v___x_2998_ = l_Lean_MessageData_ofName(v_head_2992_);
                v___x_2999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_2997_);
                crate::leanh::lean_ctor_set(v___x_2999_, 1, v___x_2998_);
                v___x_3000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3000_, 0, v___x_2999_);
                crate::leanh::lean_ctor_set(v___x_3000_, 1, v___x_2997_);
                if v_isShared_2996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2995_, 1, v_a_2990_);
                    crate::leanh::lean_ctor_set(v___x_2995_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_a_2990_);
                    v___x_3002_ = v_reuseFailAlloc_3004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2989_ = v_tail_2993_;
                v_a_2990_ = v___x_3002_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__4(
    mut v_x_3006_: *mut crate::leanh::LeanObject,
    mut v_x_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3007_) == 0 {
                    return v_x_3006_;
                } else {
                    v_key_3008_ = crate::leanh::lean_ctor_get(v_x_3007_, 0);
                    crate::leanh::lean_inc(v_key_3008_);
                    v_tail_3009_ = crate::leanh::lean_ctor_get(v_x_3007_, 2);
                    crate::leanh::lean_inc(v_tail_3009_);
                    crate::leanh::lean_dec_ref_known(v_x_3007_, 3);
                    v___x_3010_ = lean_array_push(v_x_3006_, v_key_3008_);
                    v_x_3006_ = v___x_3010_;
                    v_x_3007_ = v_tail_3009_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(
    mut v_as_3012_: *mut crate::leanh::LeanObject,
    mut v_i_3013_: usize,
    mut v_stop_3014_: usize,
    mut v_b_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: usize = 0;
    let mut v___x_3020_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3016_ = lean_usize_dec_eq(v_i_3013_, v_stop_3014_);
                if v___x_3016_ == 0 {
                    v___x_3017_ = lean_array_uget_borrowed(v_as_3012_, v_i_3013_);
                    crate::leanh::lean_inc(v___x_3017_);
                    v___x_3018_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__4(v_b_3015_, v___x_3017_);
                    v___x_3019_ = 1usize;
                    v___x_3020_ = lean_usize_add(v_i_3013_, v___x_3019_);
                    v_i_3013_ = v___x_3020_;
                    v_b_3015_ = v___x_3018_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3015_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5___boxed(
    mut v_as_3022_: *mut crate::leanh::LeanObject,
    mut v_i_3023_: *mut crate::leanh::LeanObject,
    mut v_stop_3024_: *mut crate::leanh::LeanObject,
    mut v_b_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3026_: usize = 0;
    let mut v_stop_boxed_3027_: usize = 0;
    let mut v_res_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3026_ = crate::leanh::lean_unbox_usize(v_i_3023_);
    crate::leanh::lean_dec(v_i_3023_);
    v_stop_boxed_3027_ = crate::leanh::lean_unbox_usize(v_stop_3024_);
    crate::leanh::lean_dec(v_stop_3024_);
    v_res_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_as_3022_, v_i_boxed_3026_, v_stop_boxed_3027_, v_b_3025_);
    crate::leanh::lean_dec_ref(v_as_3022_);
    return v_res_3028_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1;
    v___x_3033_ = l_Lean_MessageData_ofFormat(v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3;
    v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
    return v___x_3036_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5;
    v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(
    mut v___x_3040_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3041_: *mut crate::leanh::LeanObject,
    mut v_b_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: usize = 0;
    let mut v___x_3109_: usize = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3041_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_3040_);
                    v___x_3046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3046_, 0, v_b_3042_);
                    return v___x_3046_;
                } else {
                    v_head_3047_ = crate::leanh::lean_ctor_get(v_as_x27_3041_, 0);
                    v_tail_3048_ = crate::leanh::lean_ctor_get(v_as_x27_3041_, 1);
                    v___x_3049_ = l_Lean_NameSet_contains(v_b_3042_, v_head_3047_);
                    if v___x_3049_ == 0 {
                        crate::leanh::lean_inc_n(v_head_3047_, 2);
                        v___x_3050_ = l_Lean_NameSet_insert(v_b_3042_, v_head_3047_);
                        crate::leanh::lean_inc_ref(v___x_3040_);
                        v___x_3051_ =
                            l_Lean_Environment_find_x3f(v___x_3040_, v_head_3047_, v___x_3049_);
                        if crate::leanh::lean_obj_tag(v___x_3051_) == 1 {
                            v_val_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                            crate::leanh::lean_inc(v_val_3052_);
                            crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                            v___x_3053_ = l_Lean_ConstantInfo_type(v_val_3052_);
                            crate::leanh::lean_dec(v_val_3052_);
                            crate::leanh::lean_inc(v_head_3047_);
                            v___x_3054_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped(v___x_3053_, v_head_3047_);
                            v_size_3055_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                            v_buckets_3056_ = crate::leanh::lean_ctor_get(v___x_3054_, 1);
                            v_isSharedCheck_3114_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3054_)) as u8;
                            if v_isSharedCheck_3114_ == 0 {
                                v___x_3058_ = v___x_3054_;
                                v_isShared_3059_ = v_isSharedCheck_3114_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_buckets_3056_);
                                crate::leanh::lean_inc(v_size_3055_);
                                crate::leanh::lean_dec(v___x_3054_);
                                v___x_3058_ = crate::leanh::lean_box(0);
                                v_isShared_3059_ = v_isSharedCheck_3114_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3051_);
                            v_as_x27_3041_ = v_tail_3048_;
                            v_b_3042_ = v___x_3050_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_as_x27_3041_ = v_tail_3048_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3060_ = l_Lean_Linter_linter_checkUnivs;
                v___x_3103_ = lean_mk_empty_array_with_capacity(v_size_3055_);
                crate::leanh::lean_dec(v_size_3055_);
                v___x_3104_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3105_ = lean_array_get_size(v_buckets_3056_);
                v___x_3106_ = lean_nat_dec_lt(v___x_3104_, v___x_3105_);
                if v___x_3106_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_3056_);
                    v___y_3062_ = v___x_3103_;
                    state = 2;
                    continue;
                } else {
                    v___x_3107_ = lean_nat_dec_le(v___x_3105_, v___x_3105_);
                    if v___x_3107_ == 0 {
                        if v___x_3106_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_3056_);
                            v___y_3062_ = v___x_3103_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3108_ = 0usize;
                            v___x_3109_ = lean_usize_of_nat(v___x_3105_);
                            v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_buckets_3056_, v___x_3108_, v___x_3109_, v___x_3103_);
                            crate::leanh::lean_dec_ref(v_buckets_3056_);
                            v___y_3062_ = v___x_3110_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3111_ = 0usize;
                        v___x_3112_ = lean_usize_of_nat(v___x_3105_);
                        v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_buckets_3056_, v___x_3111_, v___x_3112_, v___x_3103_);
                        crate::leanh::lean_dec_ref(v_buckets_3056_);
                        v___y_3062_ = v___x_3113_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3063_ =
                    l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams(
                        v___y_3062_,
                    );
                v___x_3064_ = lean_array_get_size(v___x_3063_);
                v___x_3065_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3066_ = lean_nat_dec_eq(v___x_3064_, v___x_3065_);
                if v___x_3066_ == 0 {
                    v___x_3067_ = l_Lean_Elab_Command_getRef___redArg(v___y_3043_);
                    if crate::leanh::lean_obj_tag(v___x_3067_) == 0 {
                        v_a_3068_ = crate::leanh::lean_ctor_get(v___x_3067_, 0);
                        crate::leanh::lean_inc(v_a_3068_);
                        crate::leanh::lean_dec_ref_known(v___x_3067_, 1);
                        v___x_3069_ = lean_array_to_list(v___x_3063_);
                        v___x_3070_ = crate::leanh::lean_box(0);
                        v___x_3071_ = l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2(v___x_3069_, v___x_3070_);
                        v___x_3072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2);
                        v___x_3073_ = l_Lean_MessageData_joinSep(v___x_3071_, v___x_3072_);
                        v___x_3074_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1);
                        crate::leanh::lean_inc(v_head_3047_);
                        v___x_3075_ = l_Lean_MessageData_ofConstName(v_head_3047_, v___x_3066_);
                        if v_isShared_3059_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3058_, 7);
                            crate::leanh::lean_ctor_set(v___x_3058_, 1, v___x_3075_);
                            crate::leanh::lean_ctor_set(v___x_3058_, 0, v___x_3074_);
                            v___x_3077_ = v___x_3058_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3093_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3074_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3075_);
                            v___x_3077_ = v_reuseFailAlloc_3093_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3063_);
                        crate::leanh::lean_del_object(v___x_3058_);
                        crate::leanh::lean_dec(v___x_3050_);
                        crate::leanh::lean_dec_ref(v___x_3040_);
                        v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3067_, 0);
                        v_isSharedCheck_3101_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3067_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3067_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3094_);
                            crate::leanh::lean_dec(v___x_3067_);
                            v___x_3096_ = crate::leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3063_);
                    crate::leanh::lean_del_object(v___x_3058_);
                    v_as_x27_3041_ = v_tail_3048_;
                    v_b_3042_ = v___x_3050_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v___x_3078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4);
                v___x_3079_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3079_, 0, v___x_3077_);
                crate::leanh::lean_ctor_set(v___x_3079_, 1, v___x_3078_);
                v___x_3080_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3079_);
                crate::leanh::lean_ctor_set(v___x_3080_, 1, v___x_3073_);
                v___x_3081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6);
                v___x_3082_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3080_);
                crate::leanh::lean_ctor_set(v___x_3082_, 1, v___x_3081_);
                v___x_3083_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(v___x_3060_, v_a_3068_, v___x_3082_, v___y_3043_, v___y_3044_);
                crate::leanh::lean_dec(v_a_3068_);
                if crate::leanh::lean_obj_tag(v___x_3083_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3083_, 1);
                    v_as_x27_3041_ = v_tail_3048_;
                    v_b_3042_ = v___x_3050_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3050_);
                    crate::leanh::lean_dec_ref(v___x_3040_);
                    v_a_3085_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3092_ = (!crate::leanh::lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3092_ == 0 {
                        v___x_3087_ = v___x_3083_;
                        v_isShared_3088_ = v_isSharedCheck_3092_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3085_);
                        crate::leanh::lean_dec(v___x_3083_);
                        v___x_3087_ = crate::leanh::lean_box(0);
                        v_isShared_3088_ = v_isSharedCheck_3092_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3088_ == 0 {
                    v___x_3090_ = v___x_3087_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
                    v___x_3090_ = v_reuseFailAlloc_3091_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3090_;
            }
            6 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___boxed(
    mut v___x_3117_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3118_: *mut crate::leanh::LeanObject,
    mut v_b_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(
            v___x_3117_,
            v_as_x27_3118_,
            v_b_3119_,
            v___y_3120_,
            v___y_3121_,
        );
    crate::leanh::lean_dec(v___y_3121_);
    crate::leanh::lean_dec_ref(v___y_3120_);
    crate::leanh::lean_dec(v_as_x27_3118_);
    return v_res_3123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14(
    mut v___x_3124_: *mut crate::leanh::LeanObject,
    mut v_as_3125_: *mut crate::leanh::LeanObject,
    mut v_sz_3126_: usize,
    mut v_i_3127_: usize,
    mut v_b_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v_a_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: usize = 0;
    let mut v___x_3146_: usize = 0;
    let mut v_reuseFailAlloc_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_unused_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3132_ = lean_usize_dec_lt(v_i_3127_, v_sz_3126_);
                if v___x_3132_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3124_);
                    v___x_3133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3133_, 0, v_b_3128_);
                    return v___x_3133_;
                } else {
                    v_snd_3134_ = crate::leanh::lean_ctor_get(v_b_3128_, 1);
                    v_isSharedCheck_3157_ = (!crate::leanh::lean_is_exclusive(v_b_3128_)) as u8;
                    if v_isSharedCheck_3157_ == 0 {
                        v_unused_3158_ = crate::leanh::lean_ctor_get(v_b_3128_, 0);
                        crate::leanh::lean_dec(v_unused_3158_);
                        v___x_3136_ = v_b_3128_;
                        v_isShared_3137_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3134_);
                        crate::leanh::lean_dec(v_b_3128_);
                        v___x_3136_ = crate::leanh::lean_box(0);
                        v_isShared_3137_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3138_ = lean_array_uget_borrowed(v_as_3125_, v_i_3127_);
                crate::leanh::lean_inc(v_a_3138_);
                v___x_3139_ = l_Lean_Linter_getNewDecls(v_a_3138_);
                crate::leanh::lean_inc_ref(v___x_3124_);
                v___x_3140_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3124_, v___x_3139_, v_snd_3134_, v___y_3129_, v___y_3130_);
                crate::leanh::lean_dec(v___x_3139_);
                if crate::leanh::lean_obj_tag(v___x_3140_) == 0 {
                    v_a_3141_ = crate::leanh::lean_ctor_get(v___x_3140_, 0);
                    crate::leanh::lean_inc(v_a_3141_);
                    crate::leanh::lean_dec_ref_known(v___x_3140_, 1);
                    v___x_3142_ = crate::leanh::lean_box(0);
                    if v_isShared_3137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3136_, 1, v_a_3141_);
                        crate::leanh::lean_ctor_set(v___x_3136_, 0, v___x_3142_);
                        v___x_3144_ = v___x_3136_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_a_3141_);
                        v___x_3144_ = v_reuseFailAlloc_3148_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3136_);
                    crate::leanh::lean_dec_ref(v___x_3124_);
                    v_a_3149_ = crate::leanh::lean_ctor_get(v___x_3140_, 0);
                    v_isSharedCheck_3156_ = (!crate::leanh::lean_is_exclusive(v___x_3140_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v___x_3151_ = v___x_3140_;
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3149_);
                        crate::leanh::lean_dec(v___x_3140_);
                        v___x_3151_ = crate::leanh::lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3145_ = 1usize;
                v___x_3146_ = lean_usize_add(v_i_3127_, v___x_3145_);
                v_i_3127_ = v___x_3146_;
                v_b_3128_ = v___x_3144_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3152_ == 0 {
                    v___x_3154_ = v___x_3151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14___boxed(
    mut v___x_3159_: *mut crate::leanh::LeanObject,
    mut v_as_3160_: *mut crate::leanh::LeanObject,
    mut v_sz_3161_: *mut crate::leanh::LeanObject,
    mut v_i_3162_: *mut crate::leanh::LeanObject,
    mut v_b_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3167_: usize = 0;
    let mut v_i_boxed_3168_: usize = 0;
    let mut v_res_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3167_ = crate::leanh::lean_unbox_usize(v_sz_3161_);
    crate::leanh::lean_dec(v_sz_3161_);
    v_i_boxed_3168_ = crate::leanh::lean_unbox_usize(v_i_3162_);
    crate::leanh::lean_dec(v_i_3162_);
    v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14(v___x_3159_, v_as_3160_, v_sz_boxed_3167_, v_i_boxed_3168_, v_b_3163_, v___y_3164_, v___y_3165_);
    crate::leanh::lean_dec(v___y_3165_);
    crate::leanh::lean_dec_ref(v___y_3164_);
    crate::leanh::lean_dec_ref(v_as_3160_);
    return v_res_3169_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(
    mut v___x_3170_: *mut crate::leanh::LeanObject,
    mut v_as_3171_: *mut crate::leanh::LeanObject,
    mut v_sz_3172_: usize,
    mut v_i_3173_: usize,
    mut v_b_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3183_: u8 = 0;
    let mut v_a_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_unused_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3178_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
                if v___x_3178_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3170_);
                    v___x_3179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3179_, 0, v_b_3174_);
                    return v___x_3179_;
                } else {
                    v_snd_3180_ = crate::leanh::lean_ctor_get(v_b_3174_, 1);
                    v_isSharedCheck_3203_ = (!crate::leanh::lean_is_exclusive(v_b_3174_)) as u8;
                    if v_isSharedCheck_3203_ == 0 {
                        v_unused_3204_ = crate::leanh::lean_ctor_get(v_b_3174_, 0);
                        crate::leanh::lean_dec(v_unused_3204_);
                        v___x_3182_ = v_b_3174_;
                        v_isShared_3183_ = v_isSharedCheck_3203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3180_);
                        crate::leanh::lean_dec(v_b_3174_);
                        v___x_3182_ = crate::leanh::lean_box(0);
                        v_isShared_3183_ = v_isSharedCheck_3203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3184_ = lean_array_uget_borrowed(v_as_3171_, v_i_3173_);
                crate::leanh::lean_inc(v_a_3184_);
                v___x_3185_ = l_Lean_Linter_getNewDecls(v_a_3184_);
                crate::leanh::lean_inc_ref(v___x_3170_);
                v___x_3186_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3170_, v___x_3185_, v_snd_3180_, v___y_3175_, v___y_3176_);
                crate::leanh::lean_dec(v___x_3185_);
                if crate::leanh::lean_obj_tag(v___x_3186_) == 0 {
                    v_a_3187_ = crate::leanh::lean_ctor_get(v___x_3186_, 0);
                    crate::leanh::lean_inc(v_a_3187_);
                    crate::leanh::lean_dec_ref_known(v___x_3186_, 1);
                    v___x_3188_ = crate::leanh::lean_box(0);
                    if v_isShared_3183_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3182_, 1, v_a_3187_);
                        crate::leanh::lean_ctor_set(v___x_3182_, 0, v___x_3188_);
                        v___x_3190_ = v___x_3182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3188_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_a_3187_);
                        v___x_3190_ = v_reuseFailAlloc_3194_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3182_);
                    crate::leanh::lean_dec_ref(v___x_3170_);
                    v_a_3195_ = crate::leanh::lean_ctor_get(v___x_3186_, 0);
                    v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v___x_3186_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3197_ = v___x_3186_;
                        v_isShared_3198_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3195_);
                        crate::leanh::lean_dec(v___x_3186_);
                        v___x_3197_ = crate::leanh::lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3191_ = 1usize;
                v___x_3192_ = lean_usize_add(v_i_3173_, v___x_3191_);
                v___x_3193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14(v___x_3170_, v_as_3171_, v_sz_3172_, v___x_3192_, v___x_3190_, v___y_3175_, v___y_3176_);
                return v___x_3193_;
            }
            3 => {
                if v_isShared_3198_ == 0 {
                    v___x_3200_ = v___x_3197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12___boxed(
    mut v___x_3205_: *mut crate::leanh::LeanObject,
    mut v_as_3206_: *mut crate::leanh::LeanObject,
    mut v_sz_3207_: *mut crate::leanh::LeanObject,
    mut v_i_3208_: *mut crate::leanh::LeanObject,
    mut v_b_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3213_: usize = 0;
    let mut v_i_boxed_3214_: usize = 0;
    let mut v_res_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3213_ = crate::leanh::lean_unbox_usize(v_sz_3207_);
    crate::leanh::lean_dec(v_sz_3207_);
    v_i_boxed_3214_ = crate::leanh::lean_unbox_usize(v_i_3208_);
    crate::leanh::lean_dec(v_i_3208_);
    v_res_3215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(v___x_3205_, v_as_3206_, v_sz_boxed_3213_, v_i_boxed_3214_, v_b_3209_, v___y_3210_, v___y_3211_);
    crate::leanh::lean_dec(v___y_3211_);
    crate::leanh::lean_dec_ref(v___y_3210_);
    crate::leanh::lean_dec_ref(v_as_3206_);
    return v_res_3215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(
    mut v_init_3216_: *mut crate::leanh::LeanObject,
    mut v___x_3217_: *mut crate::leanh::LeanObject,
    mut v_n_3218_: *mut crate::leanh::LeanObject,
    mut v_b_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3226_: usize = 0;
    let mut v___x_3227_: usize = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v_fst_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v_a_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_vs_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3255_: usize = 0;
    let mut v___x_3256_: usize = 0;
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_fst_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3218_) == 0 {
                    v_cs_3223_ = crate::leanh::lean_ctor_get(v_n_3218_, 0);
                    v___x_3224_ = crate::leanh::lean_box(0);
                    v___x_3225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3225_, 0, v___x_3224_);
                    crate::leanh::lean_ctor_set(v___x_3225_, 1, v_b_3219_);
                    v_sz_3226_ = lean_array_size(v_cs_3223_);
                    v___x_3227_ = 0usize;
                    v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11(v_init_3216_, v___x_3217_, v_cs_3223_, v_sz_3226_, v___x_3227_, v___x_3225_, v___y_3220_, v___y_3221_);
                    if crate::leanh::lean_obj_tag(v___x_3228_) == 0 {
                        v_a_3229_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                        v_isSharedCheck_3243_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3243_ == 0 {
                            v___x_3231_ = v___x_3228_;
                            v_isShared_3232_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3229_);
                            crate::leanh::lean_dec(v___x_3228_);
                            v___x_3231_ = crate::leanh::lean_box(0);
                            v_isShared_3232_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3244_ = crate::leanh::lean_ctor_get(v___x_3228_, 0);
                        v_isSharedCheck_3251_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3251_ == 0 {
                            v___x_3246_ = v___x_3228_;
                            v_isShared_3247_ = v_isSharedCheck_3251_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3244_);
                            crate::leanh::lean_dec(v___x_3228_);
                            v___x_3246_ = crate::leanh::lean_box(0);
                            v_isShared_3247_ = v_isSharedCheck_3251_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3252_ = crate::leanh::lean_ctor_get(v_n_3218_, 0);
                    v___x_3253_ = crate::leanh::lean_box(0);
                    v___x_3254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3254_, 0, v___x_3253_);
                    crate::leanh::lean_ctor_set(v___x_3254_, 1, v_b_3219_);
                    v_sz_3255_ = lean_array_size(v_vs_3252_);
                    v___x_3256_ = 0usize;
                    v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(v___x_3217_, v_vs_3252_, v_sz_3255_, v___x_3256_, v___x_3254_, v___y_3220_, v___y_3221_);
                    if crate::leanh::lean_obj_tag(v___x_3257_) == 0 {
                        v_a_3258_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                        v_isSharedCheck_3272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3272_ == 0 {
                            v___x_3260_ = v___x_3257_;
                            v_isShared_3261_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3258_);
                            crate::leanh::lean_dec(v___x_3257_);
                            v___x_3260_ = crate::leanh::lean_box(0);
                            v_isShared_3261_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                        v_isSharedCheck_3280_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3280_ == 0 {
                            v___x_3275_ = v___x_3257_;
                            v_isShared_3276_ = v_isSharedCheck_3280_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3273_);
                            crate::leanh::lean_dec(v___x_3257_);
                            v___x_3275_ = crate::leanh::lean_box(0);
                            v_isShared_3276_ = v_isSharedCheck_3280_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3233_ = crate::leanh::lean_ctor_get(v_a_3229_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3233_) == 0 {
                    v_snd_3234_ = crate::leanh::lean_ctor_get(v_a_3229_, 1);
                    crate::leanh::lean_inc(v_snd_3234_);
                    crate::leanh::lean_dec(v_a_3229_);
                    v___x_3235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3235_, 0, v_snd_3234_);
                    if v_isShared_3232_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3235_);
                        v___x_3237_ = v___x_3231_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                        v___x_3237_ = v_reuseFailAlloc_3238_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3233_);
                    crate::leanh::lean_dec(v_a_3229_);
                    v_val_3239_ = crate::leanh::lean_ctor_get(v_fst_3233_, 0);
                    crate::leanh::lean_inc(v_val_3239_);
                    crate::leanh::lean_dec_ref_known(v_fst_3233_, 1);
                    if v_isShared_3232_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3231_, 0, v_val_3239_);
                        v___x_3241_ = v___x_3231_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_val_3239_);
                        v___x_3241_ = v_reuseFailAlloc_3242_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3237_;
            }
            3 => {
                return v___x_3241_;
            }
            4 => {
                if v_isShared_3247_ == 0 {
                    v___x_3249_ = v___x_3246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
                    v___x_3249_ = v_reuseFailAlloc_3250_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3249_;
            }
            6 => {
                v_fst_3262_ = crate::leanh::lean_ctor_get(v_a_3258_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3262_) == 0 {
                    v_snd_3263_ = crate::leanh::lean_ctor_get(v_a_3258_, 1);
                    crate::leanh::lean_inc(v_snd_3263_);
                    crate::leanh::lean_dec(v_a_3258_);
                    v___x_3264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3264_, 0, v_snd_3263_);
                    if v_isShared_3261_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3264_);
                        v___x_3266_ = v___x_3260_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
                        v___x_3266_ = v_reuseFailAlloc_3267_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3262_);
                    crate::leanh::lean_dec(v_a_3258_);
                    v_val_3268_ = crate::leanh::lean_ctor_get(v_fst_3262_, 0);
                    crate::leanh::lean_inc(v_val_3268_);
                    crate::leanh::lean_dec_ref_known(v_fst_3262_, 1);
                    if v_isShared_3261_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3260_, 0, v_val_3268_);
                        v___x_3270_ = v___x_3260_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_val_3268_);
                        v___x_3270_ = v_reuseFailAlloc_3271_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3266_;
            }
            8 => {
                return v___x_3270_;
            }
            9 => {
                if v_isShared_3276_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11(
    mut v_init_3281_: *mut crate::leanh::LeanObject,
    mut v___x_3282_: *mut crate::leanh::LeanObject,
    mut v_as_3283_: *mut crate::leanh::LeanObject,
    mut v_sz_3284_: usize,
    mut v_i_3285_: usize,
    mut v_b_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_a_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: usize = 0;
    let mut v___x_3314_: usize = 0;
    let mut v_reuseFailAlloc_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_a_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3290_ = lean_usize_dec_lt(v_i_3285_, v_sz_3284_);
                if v___x_3290_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3282_);
                    v___x_3291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3291_, 0, v_b_3286_);
                    return v___x_3291_;
                } else {
                    v_snd_3292_ = crate::leanh::lean_ctor_get(v_b_3286_, 1);
                    v_isSharedCheck_3326_ = (!crate::leanh::lean_is_exclusive(v_b_3286_)) as u8;
                    if v_isSharedCheck_3326_ == 0 {
                        v_unused_3327_ = crate::leanh::lean_ctor_get(v_b_3286_, 0);
                        crate::leanh::lean_dec(v_unused_3327_);
                        v___x_3294_ = v_b_3286_;
                        v_isShared_3295_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3292_);
                        crate::leanh::lean_dec(v_b_3286_);
                        v___x_3294_ = crate::leanh::lean_box(0);
                        v_isShared_3295_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3296_ = lean_array_uget_borrowed(v_as_3283_, v_i_3285_);
                crate::leanh::lean_inc(v_snd_3292_);
                crate::leanh::lean_inc_ref(v___x_3282_);
                v___x_3297_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3281_, v___x_3282_, v_a_3296_, v_snd_3292_, v___y_3287_, v___y_3288_);
                if crate::leanh::lean_obj_tag(v___x_3297_) == 0 {
                    v_a_3298_ = crate::leanh::lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3317_ = (!crate::leanh::lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3300_ = v___x_3297_;
                        v_isShared_3301_ = v_isSharedCheck_3317_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3298_);
                        crate::leanh::lean_dec(v___x_3297_);
                        v___x_3300_ = crate::leanh::lean_box(0);
                        v_isShared_3301_ = v_isSharedCheck_3317_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3294_);
                    crate::leanh::lean_dec(v_snd_3292_);
                    crate::leanh::lean_dec_ref(v___x_3282_);
                    v_a_3318_ = crate::leanh::lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3325_ = (!crate::leanh::lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3325_ == 0 {
                        v___x_3320_ = v___x_3297_;
                        v_isShared_3321_ = v_isSharedCheck_3325_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3318_);
                        crate::leanh::lean_dec(v___x_3297_);
                        v___x_3320_ = crate::leanh::lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3325_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3298_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_3282_);
                    v___x_3302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3302_, 0, v_a_3298_);
                    if v_isShared_3295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3302_);
                        v___x_3304_ = v___x_3294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3302_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_snd_3292_);
                        v___x_3304_ = v_reuseFailAlloc_3308_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3300_);
                    crate::leanh::lean_dec(v_snd_3292_);
                    v_a_3309_ = crate::leanh::lean_ctor_get(v_a_3298_, 0);
                    crate::leanh::lean_inc(v_a_3309_);
                    crate::leanh::lean_dec_ref_known(v_a_3298_, 1);
                    v___x_3310_ = crate::leanh::lean_box(0);
                    if v_isShared_3295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3294_, 1, v_a_3309_);
                        crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3310_);
                        v___x_3312_ = v___x_3294_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3310_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_a_3309_);
                        v___x_3312_ = v_reuseFailAlloc_3316_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3300_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3306_;
            }
            5 => {
                v___x_3313_ = 1usize;
                v___x_3314_ = lean_usize_add(v_i_3285_, v___x_3313_);
                v_i_3285_ = v___x_3314_;
                v_b_3286_ = v___x_3312_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3321_ == 0 {
                    v___x_3323_ = v___x_3320_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
                    v___x_3323_ = v_reuseFailAlloc_3324_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11___boxed(
    mut v_init_3328_: *mut crate::leanh::LeanObject,
    mut v___x_3329_: *mut crate::leanh::LeanObject,
    mut v_as_3330_: *mut crate::leanh::LeanObject,
    mut v_sz_3331_: *mut crate::leanh::LeanObject,
    mut v_i_3332_: *mut crate::leanh::LeanObject,
    mut v_b_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3337_: usize = 0;
    let mut v_i_boxed_3338_: usize = 0;
    let mut v_res_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3337_ = crate::leanh::lean_unbox_usize(v_sz_3331_);
    crate::leanh::lean_dec(v_sz_3331_);
    v_i_boxed_3338_ = crate::leanh::lean_unbox_usize(v_i_3332_);
    crate::leanh::lean_dec(v_i_3332_);
    v_res_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11(v_init_3328_, v___x_3329_, v_as_3330_, v_sz_boxed_3337_, v_i_boxed_3338_, v_b_3333_, v___y_3334_, v___y_3335_);
    crate::leanh::lean_dec(v___y_3335_);
    crate::leanh::lean_dec_ref(v___y_3334_);
    crate::leanh::lean_dec_ref(v_as_3330_);
    crate::leanh::lean_dec(v_init_3328_);
    return v_res_3339_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9___boxed(
    mut v_init_3340_: *mut crate::leanh::LeanObject,
    mut v___x_3341_: *mut crate::leanh::LeanObject,
    mut v_n_3342_: *mut crate::leanh::LeanObject,
    mut v_b_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v___y_3346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3347_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3340_, v___x_3341_, v_n_3342_, v_b_3343_, v___y_3344_, v___y_3345_);
    crate::leanh::lean_dec(v___y_3345_);
    crate::leanh::lean_dec_ref(v___y_3344_);
    crate::leanh::lean_dec_ref(v_n_3342_);
    crate::leanh::lean_dec(v_init_3340_);
    return v_res_3347_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14(
    mut v___x_3348_: *mut crate::leanh::LeanObject,
    mut v_as_3349_: *mut crate::leanh::LeanObject,
    mut v_sz_3350_: usize,
    mut v_i_3351_: usize,
    mut v_b_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v_a_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: usize = 0;
    let mut v___x_3370_: usize = 0;
    let mut v_reuseFailAlloc_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_unused_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3356_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
                if v___x_3356_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3348_);
                    v___x_3357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3357_, 0, v_b_3352_);
                    return v___x_3357_;
                } else {
                    v_snd_3358_ = crate::leanh::lean_ctor_get(v_b_3352_, 1);
                    v_isSharedCheck_3381_ = (!crate::leanh::lean_is_exclusive(v_b_3352_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v_unused_3382_ = crate::leanh::lean_ctor_get(v_b_3352_, 0);
                        crate::leanh::lean_dec(v_unused_3382_);
                        v___x_3360_ = v_b_3352_;
                        v_isShared_3361_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3358_);
                        crate::leanh::lean_dec(v_b_3352_);
                        v___x_3360_ = crate::leanh::lean_box(0);
                        v_isShared_3361_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3362_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
                crate::leanh::lean_inc(v_a_3362_);
                v___x_3363_ = l_Lean_Linter_getNewDecls(v_a_3362_);
                crate::leanh::lean_inc_ref(v___x_3348_);
                v___x_3364_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3348_, v___x_3363_, v_snd_3358_, v___y_3353_, v___y_3354_);
                crate::leanh::lean_dec(v___x_3363_);
                if crate::leanh::lean_obj_tag(v___x_3364_) == 0 {
                    v_a_3365_ = crate::leanh::lean_ctor_get(v___x_3364_, 0);
                    crate::leanh::lean_inc(v_a_3365_);
                    crate::leanh::lean_dec_ref_known(v___x_3364_, 1);
                    v___x_3366_ = crate::leanh::lean_box(0);
                    if v_isShared_3361_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3360_, 1, v_a_3365_);
                        crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3366_);
                        v___x_3368_ = v___x_3360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3366_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_a_3365_);
                        v___x_3368_ = v_reuseFailAlloc_3372_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3360_);
                    crate::leanh::lean_dec_ref(v___x_3348_);
                    v_a_3373_ = crate::leanh::lean_ctor_get(v___x_3364_, 0);
                    v_isSharedCheck_3380_ = (!crate::leanh::lean_is_exclusive(v___x_3364_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v___x_3375_ = v___x_3364_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3373_);
                        crate::leanh::lean_dec(v___x_3364_);
                        v___x_3375_ = crate::leanh::lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3369_ = 1usize;
                v___x_3370_ = lean_usize_add(v_i_3351_, v___x_3369_);
                v_i_3351_ = v___x_3370_;
                v_b_3352_ = v___x_3368_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3376_ == 0 {
                    v___x_3378_ = v___x_3375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
                    v___x_3378_ = v_reuseFailAlloc_3379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14___boxed(
    mut v___x_3383_: *mut crate::leanh::LeanObject,
    mut v_as_3384_: *mut crate::leanh::LeanObject,
    mut v_sz_3385_: *mut crate::leanh::LeanObject,
    mut v_i_3386_: *mut crate::leanh::LeanObject,
    mut v_b_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3391_: usize = 0;
    let mut v_i_boxed_3392_: usize = 0;
    let mut v_res_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3391_ = crate::leanh::lean_unbox_usize(v_sz_3385_);
    crate::leanh::lean_dec(v_sz_3385_);
    v_i_boxed_3392_ = crate::leanh::lean_unbox_usize(v_i_3386_);
    crate::leanh::lean_dec(v_i_3386_);
    v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14(v___x_3383_, v_as_3384_, v_sz_boxed_3391_, v_i_boxed_3392_, v_b_3387_, v___y_3388_, v___y_3389_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v___y_3388_);
    crate::leanh::lean_dec_ref(v_as_3384_);
    return v_res_3393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(
    mut v___x_3394_: *mut crate::leanh::LeanObject,
    mut v_as_3395_: *mut crate::leanh::LeanObject,
    mut v_sz_3396_: usize,
    mut v_i_3397_: usize,
    mut v_b_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v_a_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: usize = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3426_: u8 = 0;
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v_unused_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
                if v___x_3402_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3394_);
                    v___x_3403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3403_, 0, v_b_3398_);
                    return v___x_3403_;
                } else {
                    v_snd_3404_ = crate::leanh::lean_ctor_get(v_b_3398_, 1);
                    v_isSharedCheck_3427_ = (!crate::leanh::lean_is_exclusive(v_b_3398_)) as u8;
                    if v_isSharedCheck_3427_ == 0 {
                        v_unused_3428_ = crate::leanh::lean_ctor_get(v_b_3398_, 0);
                        crate::leanh::lean_dec(v_unused_3428_);
                        v___x_3406_ = v_b_3398_;
                        v_isShared_3407_ = v_isSharedCheck_3427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3404_);
                        crate::leanh::lean_dec(v_b_3398_);
                        v___x_3406_ = crate::leanh::lean_box(0);
                        v_isShared_3407_ = v_isSharedCheck_3427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3408_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
                crate::leanh::lean_inc(v_a_3408_);
                v___x_3409_ = l_Lean_Linter_getNewDecls(v_a_3408_);
                crate::leanh::lean_inc_ref(v___x_3394_);
                v___x_3410_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3394_, v___x_3409_, v_snd_3404_, v___y_3399_, v___y_3400_);
                crate::leanh::lean_dec(v___x_3409_);
                if crate::leanh::lean_obj_tag(v___x_3410_) == 0 {
                    v_a_3411_ = crate::leanh::lean_ctor_get(v___x_3410_, 0);
                    crate::leanh::lean_inc(v_a_3411_);
                    crate::leanh::lean_dec_ref_known(v___x_3410_, 1);
                    v___x_3412_ = crate::leanh::lean_box(0);
                    if v_isShared_3407_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3406_, 1, v_a_3411_);
                        crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3412_);
                        v___x_3414_ = v___x_3406_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3412_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_a_3411_);
                        v___x_3414_ = v_reuseFailAlloc_3418_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3406_);
                    crate::leanh::lean_dec_ref(v___x_3394_);
                    v_a_3419_ = crate::leanh::lean_ctor_get(v___x_3410_, 0);
                    v_isSharedCheck_3426_ = (!crate::leanh::lean_is_exclusive(v___x_3410_)) as u8;
                    if v_isSharedCheck_3426_ == 0 {
                        v___x_3421_ = v___x_3410_;
                        v_isShared_3422_ = v_isSharedCheck_3426_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3419_);
                        crate::leanh::lean_dec(v___x_3410_);
                        v___x_3421_ = crate::leanh::lean_box(0);
                        v_isShared_3422_ = v_isSharedCheck_3426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3415_ = 1usize;
                v___x_3416_ = lean_usize_add(v_i_3397_, v___x_3415_);
                v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14(v___x_3394_, v_as_3395_, v_sz_3396_, v___x_3416_, v___x_3414_, v___y_3399_, v___y_3400_);
                return v___x_3417_;
            }
            3 => {
                if v_isShared_3422_ == 0 {
                    v___x_3424_ = v___x_3421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
                    v___x_3424_ = v_reuseFailAlloc_3425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10___boxed(
    mut v___x_3429_: *mut crate::leanh::LeanObject,
    mut v_as_3430_: *mut crate::leanh::LeanObject,
    mut v_sz_3431_: *mut crate::leanh::LeanObject,
    mut v_i_3432_: *mut crate::leanh::LeanObject,
    mut v_b_3433_: *mut crate::leanh::LeanObject,
    mut v___y_3434_: *mut crate::leanh::LeanObject,
    mut v___y_3435_: *mut crate::leanh::LeanObject,
    mut v___y_3436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3437_: usize = 0;
    let mut v_i_boxed_3438_: usize = 0;
    let mut v_res_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3437_ = crate::leanh::lean_unbox_usize(v_sz_3431_);
    crate::leanh::lean_dec(v_sz_3431_);
    v_i_boxed_3438_ = crate::leanh::lean_unbox_usize(v_i_3432_);
    crate::leanh::lean_dec(v_i_3432_);
    v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(v___x_3429_, v_as_3430_, v_sz_boxed_3437_, v_i_boxed_3438_, v_b_3433_, v___y_3434_, v___y_3435_);
    crate::leanh::lean_dec(v___y_3435_);
    crate::leanh::lean_dec_ref(v___y_3434_);
    crate::leanh::lean_dec_ref(v_as_3430_);
    return v_res_3439_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(
    mut v___x_3440_: *mut crate::leanh::LeanObject,
    mut v_t_3441_: *mut crate::leanh::LeanObject,
    mut v_init_3442_: *mut crate::leanh::LeanObject,
    mut v___y_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v_a_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3460_: usize = 0;
    let mut v___x_3461_: usize = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v_fst_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_a_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_a_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3446_ = crate::leanh::lean_ctor_get(v_t_3441_, 0);
                v_tail_3447_ = crate::leanh::lean_ctor_get(v_t_3441_, 1);
                crate::leanh::lean_inc_ref(v___x_3440_);
                crate::leanh::lean_inc(v_init_3442_);
                v___x_3448_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3442_, v___x_3440_, v_root_3446_, v_init_3442_, v___y_3443_, v___y_3444_);
                crate::leanh::lean_dec(v_init_3442_);
                if crate::leanh::lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3485_ = (!crate::leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3451_ = v___x_3448_;
                        v_isShared_3452_ = v_isSharedCheck_3485_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3449_);
                        crate::leanh::lean_dec(v___x_3448_);
                        v___x_3451_ = crate::leanh::lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3485_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3440_);
                    v_a_3486_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3493_ = (!crate::leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3493_ == 0 {
                        v___x_3488_ = v___x_3448_;
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3486_);
                        crate::leanh::lean_dec(v___x_3448_);
                        v___x_3488_ = crate::leanh::lean_box(0);
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3449_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_3440_);
                    v_a_3453_ = crate::leanh::lean_ctor_get(v_a_3449_, 0);
                    crate::leanh::lean_inc(v_a_3453_);
                    crate::leanh::lean_dec_ref_known(v_a_3449_, 1);
                    if v_isShared_3452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3451_, 0, v_a_3453_);
                        v___x_3455_ = v___x_3451_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3456_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3453_);
                        v___x_3455_ = v_reuseFailAlloc_3456_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3451_);
                    v_a_3457_ = crate::leanh::lean_ctor_get(v_a_3449_, 0);
                    crate::leanh::lean_inc(v_a_3457_);
                    crate::leanh::lean_dec_ref_known(v_a_3449_, 1);
                    v___x_3458_ = crate::leanh::lean_box(0);
                    v___x_3459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3459_, 0, v___x_3458_);
                    crate::leanh::lean_ctor_set(v___x_3459_, 1, v_a_3457_);
                    v_sz_3460_ = lean_array_size(v_tail_3447_);
                    v___x_3461_ = 0usize;
                    v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(v___x_3440_, v_tail_3447_, v_sz_3460_, v___x_3461_, v___x_3459_, v___y_3443_, v___y_3444_);
                    if crate::leanh::lean_obj_tag(v___x_3462_) == 0 {
                        v_a_3463_ = crate::leanh::lean_ctor_get(v___x_3462_, 0);
                        v_isSharedCheck_3476_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3462_)) as u8;
                        if v_isSharedCheck_3476_ == 0 {
                            v___x_3465_ = v___x_3462_;
                            v_isShared_3466_ = v_isSharedCheck_3476_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3463_);
                            crate::leanh::lean_dec(v___x_3462_);
                            v___x_3465_ = crate::leanh::lean_box(0);
                            v_isShared_3466_ = v_isSharedCheck_3476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3477_ = crate::leanh::lean_ctor_get(v___x_3462_, 0);
                        v_isSharedCheck_3484_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3462_)) as u8;
                        if v_isSharedCheck_3484_ == 0 {
                            v___x_3479_ = v___x_3462_;
                            v_isShared_3480_ = v_isSharedCheck_3484_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3477_);
                            crate::leanh::lean_dec(v___x_3462_);
                            v___x_3479_ = crate::leanh::lean_box(0);
                            v_isShared_3480_ = v_isSharedCheck_3484_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3455_;
            }
            3 => {
                v_fst_3467_ = crate::leanh::lean_ctor_get(v_a_3463_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3467_) == 0 {
                    v_snd_3468_ = crate::leanh::lean_ctor_get(v_a_3463_, 1);
                    crate::leanh::lean_inc(v_snd_3468_);
                    crate::leanh::lean_dec(v_a_3463_);
                    if v_isShared_3466_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3465_, 0, v_snd_3468_);
                        v___x_3470_ = v___x_3465_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_snd_3468_);
                        v___x_3470_ = v_reuseFailAlloc_3471_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3467_);
                    crate::leanh::lean_dec(v_a_3463_);
                    v_val_3472_ = crate::leanh::lean_ctor_get(v_fst_3467_, 0);
                    crate::leanh::lean_inc(v_val_3472_);
                    crate::leanh::lean_dec_ref_known(v_fst_3467_, 1);
                    if v_isShared_3466_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3465_, 0, v_val_3472_);
                        v___x_3474_ = v___x_3465_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_val_3472_);
                        v___x_3474_ = v_reuseFailAlloc_3475_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3470_;
            }
            5 => {
                return v___x_3474_;
            }
            6 => {
                if v_isShared_3480_ == 0 {
                    v___x_3482_ = v___x_3479_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
                    v___x_3482_ = v_reuseFailAlloc_3483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3482_;
            }
            8 => {
                if v_isShared_3489_ == 0 {
                    v___x_3491_ = v___x_3488_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
                    v___x_3491_ = v_reuseFailAlloc_3492_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7___boxed(
    mut v___x_3494_: *mut crate::leanh::LeanObject,
    mut v_t_3495_: *mut crate::leanh::LeanObject,
    mut v_init_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(
            v___x_3494_,
            v_t_3495_,
            v_init_3496_,
            v___y_3497_,
            v___y_3498_,
        );
    crate::leanh::lean_dec(v___y_3498_);
    crate::leanh::lean_dec_ref(v___y_3497_);
    crate::leanh::lean_dec_ref(v_t_3495_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0(
    mut v_x_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: u8 = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut v_unused_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(v___y_3502_, v___y_3503_);
                v_a_3506_ = crate::leanh::lean_ctor_get(v___x_3505_, 0);
                v_isSharedCheck_3546_ = (!crate::leanh::lean_is_exclusive(v___x_3505_)) as u8;
                if v_isSharedCheck_3546_ == 0 {
                    v___x_3508_ = v___x_3505_;
                    v_isShared_3509_ = v_isSharedCheck_3546_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3506_);
                    crate::leanh::lean_dec(v___x_3505_);
                    v___x_3508_ = crate::leanh::lean_box(0);
                    v_isShared_3509_ = v_isSharedCheck_3546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3510_ = l_Lean_Linter_linter_checkUnivs;
                v___x_3511_ = l_Lean_Linter_getLinterValue(v___x_3510_, v_a_3506_);
                crate::leanh::lean_dec(v_a_3506_);
                if v___x_3511_ == 0 {
                    v___x_3512_ = crate::leanh::lean_box(0);
                    if v_isShared_3509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3512_);
                        v___x_3514_ = v___x_3508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
                        v___x_3514_ = v_reuseFailAlloc_3515_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3516_ = lean_st_ref_get(v___y_3503_);
                    v_messages_3517_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                    crate::leanh::lean_inc_ref(v_messages_3517_);
                    crate::leanh::lean_dec(v___x_3516_);
                    v___x_3518_ = l_Lean_MessageLog_hasErrors(v_messages_3517_);
                    crate::leanh::lean_dec_ref(v_messages_3517_);
                    if v___x_3518_ == 0 {
                        crate::leanh::lean_del_object(v___x_3508_);
                        v___x_3519_ = lean_st_ref_get(v___y_3503_);
                        v___x_3520_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(v___y_3503_);
                        v_a_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                        crate::leanh::lean_inc(v_a_3521_);
                        crate::leanh::lean_dec_ref(v___x_3520_);
                        v_env_3522_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                        crate::leanh::lean_inc_ref(v_env_3522_);
                        crate::leanh::lean_dec(v___x_3519_);
                        v___x_3523_ = l_Lean_NameSet_empty;
                        v___x_3524_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(v_env_3522_, v_a_3521_, v___x_3523_, v___y_3502_, v___y_3503_);
                        crate::leanh::lean_dec(v_a_3521_);
                        if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                            v_isSharedCheck_3532_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                            if v_isSharedCheck_3532_ == 0 {
                                v_unused_3533_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                                crate::leanh::lean_dec(v_unused_3533_);
                                v___x_3526_ = v___x_3524_;
                                v_isShared_3527_ = v_isSharedCheck_3532_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3524_);
                                v___x_3526_ = crate::leanh::lean_box(0);
                                v_isShared_3527_ = v_isSharedCheck_3532_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3534_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                            v_isSharedCheck_3541_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                            if v_isSharedCheck_3541_ == 0 {
                                v___x_3536_ = v___x_3524_;
                                v_isShared_3537_ = v_isSharedCheck_3541_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3534_);
                                crate::leanh::lean_dec(v___x_3524_);
                                v___x_3536_ = crate::leanh::lean_box(0);
                                v_isShared_3537_ = v_isSharedCheck_3541_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_3542_ = crate::leanh::lean_box(0);
                        if v_isShared_3509_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3542_);
                            v___x_3544_ = v___x_3508_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3545_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
                            v___x_3544_ = v_reuseFailAlloc_3545_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3514_;
            }
            3 => {
                v___x_3528_ = crate::leanh::lean_box(0);
                if v_isShared_3527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3526_, 0, v___x_3528_);
                    v___x_3530_ = v___x_3526_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
                    v___x_3530_ = v_reuseFailAlloc_3531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3530_;
            }
            5 => {
                if v_isShared_3537_ == 0 {
                    v___x_3539_ = v___x_3536_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
                    v___x_3539_ = v_reuseFailAlloc_3540_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3539_;
            }
            7 => {
                return v___x_3544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0___boxed(
    mut v_x_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ =
        l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0(v_x_3547_, v___y_3548_, v___y_3549_);
    crate::leanh::lean_dec(v___y_3549_);
    crate::leanh::lean_dec_ref(v___y_3548_);
    crate::leanh::lean_dec(v_x_3547_);
    return v_res_3551_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0(
    mut v_o_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3570_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_o_3566_, v___y_3568_);
    return v___x_3570_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___boxed(
    mut v_o_3571_: *mut crate::leanh::LeanObject,
    mut v___y_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
    mut v___y_3574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3575_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0(v_o_3571_, v___y_3572_, v___y_3573_);
    crate::leanh::lean_dec(v___y_3573_);
    crate::leanh::lean_dec_ref(v___y_3572_);
    return v_res_3575_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6(
    mut v___x_3576_: *mut crate::leanh::LeanObject,
    mut v_as_3577_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3578_: *mut crate::leanh::LeanObject,
    mut v_b_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(
            v___x_3576_,
            v_as_x27_3578_,
            v_b_3579_,
            v___y_3581_,
            v___y_3582_,
        );
    return v___x_3584_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___boxed(
    mut v___x_3585_: *mut crate::leanh::LeanObject,
    mut v_as_3586_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3587_: *mut crate::leanh::LeanObject,
    mut v_b_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6(
        v___x_3585_,
        v_as_3586_,
        v_as_x27_3587_,
        v_b_3588_,
        v_a_3589_,
        v___y_3590_,
        v___y_3591_,
    );
    crate::leanh::lean_dec(v___y_3591_);
    crate::leanh::lean_dec_ref(v___y_3590_);
    crate::leanh::lean_dec(v_as_x27_3587_);
    crate::leanh::lean_dec(v_as_3586_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13(
    mut v_msgData_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v_msgData_3594_, v___y_3596_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___boxed(
    mut v_msgData_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
    mut v___y_3601_: *mut crate::leanh::LeanObject,
    mut v___y_3602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3603_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13(v_msgData_3599_, v___y_3600_, v___y_3601_);
    crate::leanh::lean_dec(v___y_3601_);
    crate::leanh::lean_dec_ref(v___y_3600_);
    return v_res_3603_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_Linter_CheckUnivs_checkUnivsLinter;
    v___x_3606_ = l_Lean_Elab_Command_addLinter(v___x_3605_);
    return v___x_3606_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2____boxed(
    mut v_a_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_();
    return v_res_3608_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_CheckUnivs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_checkUnivs = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_checkUnivs);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_CheckUnivs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_CheckUnivs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_CheckUnivs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_CheckUnivs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_CheckUnivs(builtin);
}
