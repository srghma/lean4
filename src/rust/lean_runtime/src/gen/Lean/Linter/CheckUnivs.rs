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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 85, 110, 105, 118, 115, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,16210467313202055922 as *mut LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanStringObject<176> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 176, m_capacity: 176, m_length: 175, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 96, 99, 104, 101, 99, 107, 85, 110, 105, 118, 115, 96, 32, 108, 105, 110, 116, 101, 114, 44, 32, 119, 104, 105, 99, 104, 32, 119, 97, 114, 110, 115, 32, 119, 104, 101, 110, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 104, 97, 115, 32, 97, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 116, 104, 97, 116, 32, 111, 110, 108, 121, 32, 101, 118, 101, 114, 32, 111, 99, 99, 117, 114, 115, 32, 105, 110, 32, 97, 32, 96, 109, 97, 120, 32, 117, 32, 118, 96, 32, 116, 111, 103, 101, 116, 104, 101, 114, 32, 119, 105, 116, 104, 32, 97, 110, 111, 116, 104, 101, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 44, 32, 110, 101, 118, 101, 114, 32, 111, 110, 32, 105, 116, 115, 32, 111, 119, 110, 46, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,12426330975265000841 as *mut LeanObject] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0: u64 = 0;
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 95, 0]};
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0_value
) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0_value) as *mut LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [96, 58, 32, 117, 110, 105, 118, 101, 114, 115, 101, 115, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5_value: LeanStringObject<132> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 132, m_capacity: 132, m_length: 131, m_data: [32, 111, 110, 108, 121, 32, 111, 99, 99, 117, 114, 32, 116, 111, 103, 101, 116, 104, 101, 114, 46, 32, 84, 104, 105, 115, 32, 117, 115, 117, 97, 108, 108, 121, 32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 97, 32, 96, 109, 97, 120, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32, 119, 104, 101, 114, 101, 32, 110, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 115, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 115, 32, 97, 112, 112, 101, 97, 114, 32, 111, 110, 32, 116, 104, 101, 105, 114, 32, 111, 119, 110, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value)
        as *mut LeanObject;
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__2_value)
                as *mut LeanObject,
            17211735266089129274 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__3_value)
                as *mut LeanObject,
            7222886008983397929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Linter_CheckUnivs_checkUnivsLinter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_CheckUnivs_checkUnivsLinter___closed__5_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(
    mut v_name_1805_: *mut LeanObject,
    mut v_decl_1806_: *mut LeanObject,
    mut v_ref_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_unused_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1809_ = lean_ctor_get(v_decl_1806_, 0);
                v_descr_1810_ = lean_ctor_get(v_decl_1806_, 1);
                v_deprecation_x3f_1811_ = lean_ctor_get(v_decl_1806_, 2);
                v___x_1812_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1813_ = (lean_unbox(v_defValue_1809_) as u8);
                lean_ctor_set_uint8(v___x_1812_, 0 as u32, v___x_1813_);
                lean_inc(v_deprecation_x3f_1811_);
                lean_inc_ref(v_descr_1810_);
                lean_inc_n(v_name_1805_, 2);
                v___x_1814_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1814_, 0, v_name_1805_);
                lean_ctor_set(v___x_1814_, 1, v_ref_1807_);
                lean_ctor_set(v___x_1814_, 2, v___x_1812_);
                lean_ctor_set(v___x_1814_, 3, v_descr_1810_);
                lean_ctor_set(v___x_1814_, 4, v_deprecation_x3f_1811_);
                v___x_1815_ = lean_register_option(v_name_1805_, v___x_1814_);
                if lean_obj_tag(v___x_1815_) == 0 {
                    v_isSharedCheck_1823_ = (!lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v_unused_1824_ = lean_ctor_get(v___x_1815_, 0);
                        lean_dec(v_unused_1824_);
                        v___x_1817_ = v___x_1815_;
                        v_isShared_1818_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1815_);
                        v___x_1817_ = lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1805_);
                    v_a_1825_ = lean_ctor_get(v___x_1815_, 0);
                    v_isSharedCheck_1832_ = (!lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1832_ == 0 {
                        v___x_1827_ = v___x_1815_;
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1825_);
                        lean_dec(v___x_1815_);
                        v___x_1827_ = lean_box(0);
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1809_);
                v___x_1819_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1819_, 0, v_name_1805_);
                lean_ctor_set(v___x_1819_, 1, v_defValue_1809_);
                if v_isShared_1818_ == 0 {
                    lean_ctor_set(v___x_1817_, 0, v___x_1819_);
                    v___x_1821_ = v___x_1817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
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
                    v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
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
    mut v_name_1833_: *mut LeanObject,
    mut v_decl_1834_: *mut LeanObject,
    mut v_ref_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1837_: *mut LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(v_name_1833_, v_decl_1834_, v_ref_1835_);
    lean_dec_ref(v_decl_1834_);
    return v_res_1837_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1857_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1858_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1859_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_;
    v___x_1860_ = l_Lean_Option_register___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4__spec__0(v___x_1857_, v___x_1858_, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4____boxed(
    mut v_a_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1862_: *mut LeanObject = core::ptr::null_mut();
    v_res_1862_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_();
    return v_res_1862_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0()
-> u64 {
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u64 = 0;
    v___x_1863_ = lean_unsigned_to_nat(1723);
    v___x_1864_ = lean_uint64_of_nat(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(
    mut v_as_1865_: *mut LeanObject,
    mut v_i_1866_: usize,
    mut v_stop_1867_: usize,
    mut v_b_1868_: u64,
) -> u64 {
    let mut v___y_1870_: u64 = 0;
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: usize = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u64 = 0;
    let mut v_hash_1878_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1875_ = lean_usize_dec_eq(v_i_1866_, v_stop_1867_);
                if v___x_1875_ == 0 {
                    v___x_1876_ = lean_array_uget_borrowed(v_as_1865_, v_i_1866_);
                    if lean_obj_tag(v___x_1876_) == 0 {
                        v___x_1877_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2___closed__0);
                        v___y_1870_ = v___x_1877_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1878_ = lean_ctor_get_uint64(
                            v___x_1876_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_as_1879_: *mut LeanObject,
    mut v_i_1880_: *mut LeanObject,
    mut v_stop_1881_: *mut LeanObject,
    mut v_b_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1883_: usize = 0;
    let mut v_stop_boxed_1884_: usize = 0;
    let mut v_b_boxed_1885_: u64 = 0;
    let mut v_res_1886_: u64 = 0;
    let mut v_r_1887_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1883_ = lean_unbox_usize(v_i_1880_);
    lean_dec(v_i_1880_);
    v_stop_boxed_1884_ = lean_unbox_usize(v_stop_1881_);
    lean_dec(v_stop_1881_);
    v_b_boxed_1885_ = lean_unbox_uint64(v_b_1882_);
    lean_dec_ref(v_b_1882_);
    v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__2(v_as_1879_, v_i_boxed_1883_, v_stop_boxed_1884_, v_b_boxed_1885_);
    lean_dec_ref(v_as_1879_);
    v_r_1887_ = lean_box_uint64(v_res_1886_);
    return v_r_1887_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_1888_: *mut LeanObject,
    mut v_x_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u64 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v_x_1889_) == 0 {
                    return v_x_1888_;
                } else {
                    v_key_1890_ = lean_ctor_get(v_x_1889_, 0);
                    v_value_1891_ = lean_ctor_get(v_x_1889_, 1);
                    v_tail_1892_ = lean_ctor_get(v_x_1889_, 2);
                    v_isSharedCheck_1927_ = (!lean_is_exclusive(v_x_1889_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1894_ = v_x_1889_;
                        v_isShared_1895_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1892_);
                        lean_inc(v_value_1891_);
                        lean_inc(v_key_1890_);
                        lean_dec(v_x_1889_);
                        v___x_1894_ = lean_box(0);
                        v_isShared_1895_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1896_ = lean_array_get_size(v_x_1888_);
                v___x_1916_ = 7u64;
                v___x_1917_ = lean_unsigned_to_nat(0);
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
                lean_inc(v___x_1910_);
                if v_isShared_1895_ == 0 {
                    lean_ctor_set(v___x_1894_, 2, v___x_1910_);
                    v___x_1912_ = v___x_1894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_key_1890_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_value_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___x_1910_);
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
    mut v_i_1928_: *mut LeanObject,
    mut v_source_1929_: *mut LeanObject,
    mut v_target_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v_es_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = lean_array_get_size(v_source_1929_);
                v___x_1932_ = lean_nat_dec_lt(v_i_1928_, v___x_1931_);
                if v___x_1932_ == 0 {
                    lean_dec_ref(v_source_1929_);
                    lean_dec(v_i_1928_);
                    return v_target_1930_;
                } else {
                    v_es_1933_ = lean_array_fget(v_source_1929_, v_i_1928_);
                    v___x_1934_ = lean_box(0);
                    v_source_1935_ = lean_array_fset(v_source_1929_, v_i_1928_, v___x_1934_);
                    v_target_1936_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1930_, v_es_1933_);
                    v___x_1937_ = lean_unsigned_to_nat(1);
                    v___x_1938_ = lean_nat_add(v_i_1928_, v___x_1937_);
                    lean_dec(v_i_1928_);
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
    mut v_data_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    v___x_1941_ = lean_array_get_size(v_data_1940_);
    v___x_1942_ = lean_unsigned_to_nat(2);
    v_nbuckets_1943_ = lean_nat_mul(v___x_1941_, v___x_1942_);
    v___x_1944_ = lean_unsigned_to_nat(0);
    v___x_1945_ = lean_box(0);
    v___x_1946_ = lean_mk_array(v_nbuckets_1943_, v___x_1945_);
    v___x_1947_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3___redArg(v___x_1944_, v_data_1940_, v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(
    mut v_xs_1948_: *mut LeanObject,
    mut v_ys_1949_: *mut LeanObject,
    mut v_x_1950_: *mut LeanObject,
) -> u8 {
    let mut v_zero_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1952_: u8 = 0;
    let mut v_one_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1951_ = lean_unsigned_to_nat(0);
                v_isZero_1952_ = lean_nat_dec_eq(v_x_1950_, v_zero_1951_);
                if v_isZero_1952_ == 1 {
                    lean_dec(v_x_1950_);
                    return v_isZero_1952_;
                } else {
                    v_one_1953_ = lean_unsigned_to_nat(1);
                    v_n_1954_ = lean_nat_sub(v_x_1950_, v_one_1953_);
                    lean_dec(v_x_1950_);
                    v___x_1955_ = lean_array_fget_borrowed(v_xs_1948_, v_n_1954_);
                    v___x_1956_ = lean_array_fget_borrowed(v_ys_1949_, v_n_1954_);
                    v___x_1957_ = lean_name_eq(v___x_1955_, v___x_1956_);
                    if v___x_1957_ == 0 {
                        lean_dec(v_n_1954_);
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
    mut v_xs_1959_: *mut LeanObject,
    mut v_ys_1960_: *mut LeanObject,
    mut v_x_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1962_: u8 = 0;
    let mut v_r_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1962_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(v_xs_1959_, v_ys_1960_, v_x_1961_);
    lean_dec_ref(v_ys_1960_);
    lean_dec_ref(v_xs_1959_);
    v_r_1963_ = lean_box((v_res_1962_) as usize);
    return v_r_1963_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(
    mut v_a_1964_: *mut LeanObject,
    mut v_x_1965_: *mut LeanObject,
) -> u8 {
    let mut v___x_1966_: u8 = 0;
    let mut v_key_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1965_) == 0 {
                    v___x_1966_ = 0;
                    return v___x_1966_;
                } else {
                    v_key_1967_ = lean_ctor_get(v_x_1965_, 0);
                    v_tail_1968_ = lean_ctor_get(v_x_1965_, 2);
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
    mut v_a_1975_: *mut LeanObject,
    mut v_x_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: u8 = 0;
    let mut v_r_1978_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(v_a_1975_, v_x_1976_);
    lean_dec(v_x_1976_);
    lean_dec_ref(v_a_1975_);
    v_r_1978_ = lean_box((v_res_1977_) as usize);
    return v_r_1978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(
    mut v_m_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_b_1981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v_val_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_unused_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u64 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
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
                v_size_1982_ = lean_ctor_get(v_m_1979_, 0);
                v_buckets_1983_ = lean_ctor_get(v_m_1979_, 1);
                v___x_1984_ = lean_array_get_size(v_buckets_1983_);
                v___x_2023_ = 7u64;
                v___x_2024_ = lean_unsigned_to_nat(0);
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
                    lean_inc_ref(v_buckets_1983_);
                    lean_inc(v_size_1982_);
                    v_isSharedCheck_2020_ = (!lean_is_exclusive(v_m_1979_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v_unused_2021_ = lean_ctor_get(v_m_1979_, 1);
                        lean_dec(v_unused_2021_);
                        v_unused_2022_ = lean_ctor_get(v_m_1979_, 0);
                        lean_dec(v_unused_2022_);
                        v___x_2001_ = v_m_1979_;
                        v_isShared_2002_ = v_isSharedCheck_2020_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1979_);
                        v___x_2001_ = lean_box(0);
                        v_isShared_2002_ = v_isSharedCheck_2020_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1981_);
                    lean_dec_ref(v_a_1980_);
                    return v_m_1979_;
                }
            }
            2 => {
                v___x_2003_ = lean_unsigned_to_nat(1);
                v_size_x27_2004_ = lean_nat_add(v_size_1982_, v___x_2003_);
                lean_dec(v_size_1982_);
                lean_inc(v_bkt_1998_);
                v___x_2005_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2005_, 0, v_a_1980_);
                lean_ctor_set(v___x_2005_, 1, v_b_1981_);
                lean_ctor_set(v___x_2005_, 2, v_bkt_1998_);
                v_buckets_x27_2006_ = lean_array_uset(v_buckets_1983_, v___x_1997_, v___x_2005_);
                v___x_2007_ = lean_unsigned_to_nat(4);
                v___x_2008_ = lean_nat_mul(v_size_x27_2004_, v___x_2007_);
                v___x_2009_ = lean_unsigned_to_nat(3);
                v___x_2010_ = lean_nat_div(v___x_2008_, v___x_2009_);
                lean_dec(v___x_2008_);
                v___x_2011_ = lean_array_get_size(v_buckets_x27_2006_);
                v___x_2012_ = lean_nat_dec_le(v___x_2010_, v___x_2011_);
                lean_dec(v___x_2010_);
                if v___x_2012_ == 0 {
                    v_val_2013_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1___redArg(v_buckets_x27_2006_);
                    if v_isShared_2002_ == 0 {
                        lean_ctor_set(v___x_2001_, 1, v_val_2013_);
                        lean_ctor_set(v___x_2001_, 0, v_size_x27_2004_);
                        v___x_2015_ = v___x_2001_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_size_x27_2004_);
                        lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_val_2013_);
                        v___x_2015_ = v_reuseFailAlloc_2016_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2002_ == 0 {
                        lean_ctor_set(v___x_2001_, 1, v_buckets_x27_2006_);
                        lean_ctor_set(v___x_2001_, 0, v_size_x27_2004_);
                        v___x_2018_ = v___x_2001_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_size_x27_2004_);
                        lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_buckets_x27_2006_);
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
-> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = lean_box(0);
    v___x_2035_ = lean_unsigned_to_nat(16);
    v___x_2036_ = lean_mk_array(v___x_2035_, v___x_2034_);
    return v___x_2036_;
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    v___x_2037_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__0);
    v___x_2038_ = lean_unsigned_to_nat(0);
    v___x_2039_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2039_, 0, v___x_2038_);
    lean_ctor_set(v___x_2039_, 1, v___x_2037_);
    return v___x_2039_;
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
    v___x_2043_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__1);
    v___x_2044_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    lean_ctor_set(v___x_2044_, 1, v___x_2043_);
    lean_ctor_set(v___x_2044_, 2, v___x_2042_);
    return v___x_2044_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1(
    mut v_x_2045_: *mut LeanObject,
    mut v_x_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2046_) == 0 {
                    return v_x_2045_;
                } else {
                    v_head_2047_ = lean_ctor_get(v_x_2046_, 0);
                    lean_inc(v_head_2047_);
                    v_tail_2048_ = lean_ctor_get(v_x_2046_, 1);
                    lean_inc(v_tail_2048_);
                    lean_dec_ref_known(v_x_2046_, 2);
                    v___x_2049_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3);
                    v___x_2050_ = l_Lean_CollectLevelParams_visitLevel(v_head_2047_, v___x_2049_);
                    v_params_2051_ = lean_ctor_get(v___x_2050_, 2);
                    lean_inc_ref(v_params_2051_);
                    lean_dec_ref(v___x_2050_);
                    v___x_2052_ = lean_box(0);
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
    mut v_us_2055_: *mut LeanObject,
    mut v_____r_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_st_ref_take(v___y_2057_);
    v___x_2060_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1(v___x_2059_, v_us_2055_);
    v___x_2061_ = lean_st_ref_set(v___y_2057_, v___x_2060_);
    v___x_2062_ = lean_box(0);
    return v___x_2062_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0___boxed(
    mut v_us_2063_: *mut LeanObject,
    mut v_____r_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2067_: *mut LeanObject = core::ptr::null_mut();
    v_res_2067_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(
            v_us_2063_,
            v_____r_2064_,
            v___y_2065_,
        );
    lean_dec(v___y_2065_);
    return v_res_2067_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    v___x_2069_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0;
    v___x_2070_ = lean_string_utf8_byte_size(v___x_2069_);
    return v___x_2070_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1(
    mut v_nm_u2080_2071_: *mut LeanObject,
    mut v_e_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
) -> u8 {
    let mut v___x_2076_: u8 = 0;
    let mut v___y_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: u8 = 0;
    let mut v_pre_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: u8 = 0;
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2072_) {
                3 => {
                    v_u_2079_ = lean_ctor_get(v_e_2072_, 0);
                    lean_inc(v_u_2079_);
                    lean_dec_ref_known(v_e_2072_, 1);
                    v___x_2080_ = lean_st_ref_take(v___y_2073_);
                    v___x_2081_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__3);
                    v___x_2082_ = l_Lean_CollectLevelParams_visitLevel(v_u_2079_, v___x_2081_);
                    v_params_2083_ = lean_ctor_get(v___x_2082_, 2);
                    lean_inc_ref(v_params_2083_);
                    lean_dec_ref(v___x_2082_);
                    v___x_2084_ = lean_box(0);
                    v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(v___x_2080_, v_params_2083_, v___x_2084_);
                    v___x_2086_ = lean_st_ref_set(v___y_2073_, v___x_2085_);
                    state = 1;
                    continue;
                }
                4 => {
                    v_declName_2087_ = lean_ctor_get(v_e_2072_, 0);
                    lean_inc(v_declName_2087_);
                    v_us_2088_ = lean_ctor_get(v_e_2072_, 1);
                    lean_inc(v_us_2088_);
                    lean_dec_ref_known(v_e_2072_, 2);
                    if lean_obj_tag(v_declName_2087_) == 1 {
                        v_pre_2094_ = lean_ctor_get(v_declName_2087_, 0);
                        lean_inc(v_pre_2094_);
                        v_str_2095_ = lean_ctor_get(v_declName_2087_, 1);
                        lean_inc_ref(v_str_2095_);
                        lean_dec_ref_known(v_declName_2087_, 2);
                        v___x_2096_ = lean_name_eq(v_pre_2094_, v_nm_u2080_2071_);
                        lean_dec(v_pre_2094_);
                        if v___x_2096_ == 0 {
                            lean_dec_ref(v_str_2095_);
                            v___y_2093_ = v___x_2096_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2097_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__0;
                            v___x_2098_ = lean_string_utf8_byte_size(v_str_2095_);
                            v___x_2099_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___closed__1);
                            v___x_2100_ = lean_nat_dec_le(v___x_2099_, v___x_2098_);
                            if v___x_2100_ == 0 {
                                lean_dec_ref(v_str_2095_);
                                state = 3;
                                continue;
                            } else {
                                v___x_2101_ = lean_unsigned_to_nat(0);
                                v___x_2102_ = lean_string_memcmp(
                                    v_str_2095_,
                                    v___x_2097_,
                                    v___x_2101_,
                                    v___x_2101_,
                                    v___x_2099_,
                                );
                                lean_dec_ref(v_str_2095_);
                                v___y_2093_ = v___x_2102_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_declName_2087_);
                        v___x_2103_ = lean_box(0);
                        v___x_2104_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__0(v_us_2088_, v___x_2103_, v___y_2073_);
                        v___y_2078_ = v___x_2104_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_e_2072_);
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
                v___x_2090_ = lean_box(0);
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
                    lean_dec(v_us_2088_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___boxed(
    mut v_nm_u2080_2105_: *mut LeanObject,
    mut v_e_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2109_: u8 = 0;
    let mut v_r_2110_: *mut LeanObject = core::ptr::null_mut();
    v_res_2109_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1(
            v_nm_u2080_2105_,
            v_e_2106_,
            v___y_2107_,
        );
    lean_dec(v___y_2107_);
    lean_dec(v_nm_u2080_2105_);
    v_r_2110_ = lean_box((v_res_2109_) as usize);
    return v_r_2110_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(
    mut v_a_2111_: *mut LeanObject,
    mut v_x_2112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2112_) == 0 {
                    v___x_2113_ = lean_box(0);
                    return v___x_2113_;
                } else {
                    v_key_2114_ = lean_ctor_get(v_x_2112_, 0);
                    v_value_2115_ = lean_ctor_get(v_x_2112_, 1);
                    v_tail_2116_ = lean_ctor_get(v_x_2112_, 2);
                    v___x_2117_ = lean_expr_eqv(v_key_2114_, v_a_2111_);
                    if v___x_2117_ == 0 {
                        v_x_2112_ = v_tail_2116_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2115_);
                        v___x_2119_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2119_, 0, v_value_2115_);
                        return v___x_2119_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_a_2120_: *mut LeanObject,
    mut v_x_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2122_: *mut LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(v_a_2120_, v_x_2121_);
    lean_dec(v_x_2121_);
    lean_dec_ref(v_a_2120_);
    return v_res_2122_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(
    mut v_m_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2125_ = lean_ctor_get(v_m_2123_, 1);
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
    mut v_m_2141_: *mut LeanObject,
    mut v_a_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2143_: *mut LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v_m_2141_, v_a_2142_);
    lean_dec_ref(v_a_2142_);
    lean_dec_ref(v_m_2141_);
    return v_res_2143_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(
    mut v_a_2144_: *mut LeanObject,
    mut v_b_2145_: *mut LeanObject,
    mut v_x_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2153_: u8 = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2146_) == 0 {
                    lean_dec(v_b_2145_);
                    lean_dec_ref(v_a_2144_);
                    return v_x_2146_;
                } else {
                    v_key_2147_ = lean_ctor_get(v_x_2146_, 0);
                    v_value_2148_ = lean_ctor_get(v_x_2146_, 1);
                    v_tail_2149_ = lean_ctor_get(v_x_2146_, 2);
                    v_isSharedCheck_2161_ = (!lean_is_exclusive(v_x_2146_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2151_ = v_x_2146_;
                        v_isShared_2152_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2149_);
                        lean_inc(v_value_2148_);
                        lean_inc(v_key_2147_);
                        lean_dec(v_x_2146_);
                        v___x_2151_ = lean_box(0);
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
                        lean_ctor_set(v___x_2151_, 2, v___x_2154_);
                        v___x_2156_ = v___x_2151_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_key_2147_);
                        lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_value_2148_);
                        lean_ctor_set(v_reuseFailAlloc_2157_, 2, v___x_2154_);
                        v___x_2156_ = v_reuseFailAlloc_2157_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2148_);
                    lean_dec(v_key_2147_);
                    if v_isShared_2152_ == 0 {
                        lean_ctor_set(v___x_2151_, 1, v_b_2145_);
                        lean_ctor_set(v___x_2151_, 0, v_a_2144_);
                        v___x_2159_ = v___x_2151_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2144_);
                        lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_b_2145_);
                        lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_tail_2149_);
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
    mut v_x_2162_: *mut LeanObject,
    mut v_x_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2163_) == 0 {
                    return v_x_2162_;
                } else {
                    v_key_2164_ = lean_ctor_get(v_x_2163_, 0);
                    v_value_2165_ = lean_ctor_get(v_x_2163_, 1);
                    v_tail_2166_ = lean_ctor_get(v_x_2163_, 2);
                    v_isSharedCheck_2189_ = (!lean_is_exclusive(v_x_2163_)) as u8;
                    if v_isSharedCheck_2189_ == 0 {
                        v___x_2168_ = v_x_2163_;
                        v_isShared_2169_ = v_isSharedCheck_2189_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2166_);
                        lean_inc(v_value_2165_);
                        lean_inc(v_key_2164_);
                        lean_dec(v_x_2163_);
                        v___x_2168_ = lean_box(0);
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
                lean_inc(v___x_2183_);
                if v_isShared_2169_ == 0 {
                    lean_ctor_set(v___x_2168_, 2, v___x_2183_);
                    v___x_2185_ = v___x_2168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_key_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_value_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 2, v___x_2183_);
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
    mut v_i_2190_: *mut LeanObject,
    mut v_source_2191_: *mut LeanObject,
    mut v_target_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v_es_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = lean_array_get_size(v_source_2191_);
                v___x_2194_ = lean_nat_dec_lt(v_i_2190_, v___x_2193_);
                if v___x_2194_ == 0 {
                    lean_dec_ref(v_source_2191_);
                    lean_dec(v_i_2190_);
                    return v_target_2192_;
                } else {
                    v_es_2195_ = lean_array_fget(v_source_2191_, v_i_2190_);
                    v___x_2196_ = lean_box(0);
                    v_source_2197_ = lean_array_fset(v_source_2191_, v_i_2190_, v___x_2196_);
                    v_target_2198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14___redArg(v_target_2192_, v_es_2195_);
                    v___x_2199_ = lean_unsigned_to_nat(1);
                    v___x_2200_ = lean_nat_add(v_i_2190_, v___x_2199_);
                    lean_dec(v_i_2190_);
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
    mut v_data_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = lean_array_get_size(v_data_2202_);
    v___x_2204_ = lean_unsigned_to_nat(2);
    v_nbuckets_2205_ = lean_nat_mul(v___x_2203_, v___x_2204_);
    v___x_2206_ = lean_unsigned_to_nat(0);
    v___x_2207_ = lean_box(0);
    v___x_2208_ = lean_mk_array(v_nbuckets_2205_, v___x_2207_);
    v___x_2209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13___redArg(v___x_2206_, v_data_2202_, v___x_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(
    mut v_a_2210_: *mut LeanObject,
    mut v_x_2211_: *mut LeanObject,
) -> u8 {
    let mut v___x_2212_: u8 = 0;
    let mut v_key_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2211_) == 0 {
                    v___x_2212_ = 0;
                    return v___x_2212_;
                } else {
                    v_key_2213_ = lean_ctor_get(v_x_2211_, 0);
                    v_tail_2214_ = lean_ctor_get(v_x_2211_, 2);
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
    mut v_a_2217_: *mut LeanObject,
    mut v_x_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2219_: u8 = 0;
    let mut v_r_2220_: *mut LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(v_a_2217_, v_x_2218_);
    lean_dec(v_x_2218_);
    lean_dec_ref(v_a_2217_);
    v_r_2220_ = lean_box((v_res_2219_) as usize);
    return v_r_2220_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6___redArg(
    mut v_m_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_b_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v_val_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2224_ = lean_ctor_get(v_m_2221_, 0);
                v_buckets_2225_ = lean_ctor_get(v_m_2221_, 1);
                v_isSharedCheck_2268_ = (!lean_is_exclusive(v_m_2221_)) as u8;
                if v_isSharedCheck_2268_ == 0 {
                    v___x_2227_ = v_m_2221_;
                    v_isShared_2228_ = v_isSharedCheck_2268_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2225_);
                    lean_inc(v_size_2224_);
                    lean_dec(v_m_2221_);
                    v___x_2227_ = lean_box(0);
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
                    v___x_2244_ = lean_unsigned_to_nat(1);
                    v_size_x27_2245_ = lean_nat_add(v_size_2224_, v___x_2244_);
                    lean_dec(v_size_2224_);
                    lean_inc(v_bkt_2242_);
                    v___x_2246_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2246_, 0, v_a_2222_);
                    lean_ctor_set(v___x_2246_, 1, v_b_2223_);
                    lean_ctor_set(v___x_2246_, 2, v_bkt_2242_);
                    v_buckets_x27_2247_ =
                        lean_array_uset(v_buckets_2225_, v___x_2241_, v___x_2246_);
                    v___x_2248_ = lean_unsigned_to_nat(4);
                    v___x_2249_ = lean_nat_mul(v_size_x27_2245_, v___x_2248_);
                    v___x_2250_ = lean_unsigned_to_nat(3);
                    v___x_2251_ = lean_nat_div(v___x_2249_, v___x_2250_);
                    lean_dec(v___x_2249_);
                    v___x_2252_ = lean_array_get_size(v_buckets_x27_2247_);
                    v___x_2253_ = lean_nat_dec_le(v___x_2251_, v___x_2252_);
                    lean_dec(v___x_2251_);
                    if v___x_2253_ == 0 {
                        v_val_2254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11___redArg(v_buckets_x27_2247_);
                        if v_isShared_2228_ == 0 {
                            lean_ctor_set(v___x_2227_, 1, v_val_2254_);
                            lean_ctor_set(v___x_2227_, 0, v_size_x27_2245_);
                            v___x_2256_ = v___x_2227_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_size_x27_2245_);
                            lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_val_2254_);
                            v___x_2256_ = v_reuseFailAlloc_2257_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2228_ == 0 {
                            lean_ctor_set(v___x_2227_, 1, v_buckets_x27_2247_);
                            lean_ctor_set(v___x_2227_, 0, v_size_x27_2245_);
                            v___x_2259_ = v___x_2227_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_size_x27_2245_);
                            lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_buckets_x27_2247_);
                            v___x_2259_ = v_reuseFailAlloc_2260_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2242_);
                    v___x_2261_ = lean_box(0);
                    v_buckets_x27_2262_ =
                        lean_array_uset(v_buckets_2225_, v___x_2241_, v___x_2261_);
                    v___x_2263_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(v_a_2222_, v_b_2223_, v_bkt_2242_);
                    v___x_2264_ = lean_array_uset(v_buckets_x27_2262_, v___x_2241_, v___x_2263_);
                    if v_isShared_2228_ == 0 {
                        lean_ctor_set(v___x_2227_, 1, v___x_2264_);
                        v___x_2266_ = v___x_2227_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_size_2224_);
                        lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
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
    mut v_g_2269_: *mut LeanObject,
    mut v_e_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2281_ = lean_st_ref_get(v_a_2271_);
                v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v___x_2281_, v_e_2270_);
                lean_dec(v___x_2281_);
                if lean_obj_tag(v___x_2282_) == 0 {
                    lean_inc_ref(v_g_2269_);
                    lean_inc(v___y_2272_);
                    lean_inc_ref(v_e_2270_);
                    v___x_2283_ = lean_apply_3(v_g_2269_, v_e_2270_, v___y_2272_, lean_box(0));
                    v___x_2290_ = (lean_unbox(v___x_2283_) as u8);
                    if v___x_2290_ == 0 {
                        lean_dec_ref(v_g_2269_);
                        v___x_2291_ = lean_box(0);
                        v_val_2275_ = v___x_2291_;
                        state = 1;
                        continue;
                    } else {
                        match lean_obj_tag(v_e_2270_) {
                            7 => {
                                v_binderType_2292_ = lean_ctor_get(v_e_2270_, 1);
                                v_body_2293_ = lean_ctor_get(v_e_2270_, 2);
                                lean_inc_ref(v_body_2293_);
                                lean_inc_ref(v_binderType_2292_);
                                v_d_2285_ = v_binderType_2292_;
                                v_b_2286_ = v_body_2293_;
                                v___y_2287_ = v_a_2271_;
                                state = 3;
                                continue;
                            }
                            6 => {
                                v_binderType_2294_ = lean_ctor_get(v_e_2270_, 1);
                                v_body_2295_ = lean_ctor_get(v_e_2270_, 2);
                                lean_inc_ref(v_body_2295_);
                                lean_inc_ref(v_binderType_2294_);
                                v_d_2285_ = v_binderType_2294_;
                                v_b_2286_ = v_body_2295_;
                                v___y_2287_ = v_a_2271_;
                                state = 3;
                                continue;
                            }
                            8 => {
                                v_type_2296_ = lean_ctor_get(v_e_2270_, 1);
                                v_value_2297_ = lean_ctor_get(v_e_2270_, 2);
                                v_body_2298_ = lean_ctor_get(v_e_2270_, 3);
                                lean_inc_ref(v_type_2296_);
                                lean_inc_ref_n(v_g_2269_, 2);
                                v___x_2299_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_type_2296_, v_a_2271_, v___y_2272_);
                                lean_inc_ref(v_value_2297_);
                                v___x_2300_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_value_2297_, v_a_2271_, v___y_2272_);
                                lean_inc_ref(v_body_2298_);
                                v___x_2301_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_body_2298_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2301_;
                                state = 2;
                                continue;
                            }
                            5 => {
                                v_fn_2302_ = lean_ctor_get(v_e_2270_, 0);
                                v_arg_2303_ = lean_ctor_get(v_e_2270_, 1);
                                lean_inc_ref(v_fn_2302_);
                                lean_inc_ref(v_g_2269_);
                                v___x_2304_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_fn_2302_, v_a_2271_, v___y_2272_);
                                lean_inc_ref(v_arg_2303_);
                                v___x_2305_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_arg_2303_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2305_;
                                state = 2;
                                continue;
                            }
                            10 => {
                                v_expr_2306_ = lean_ctor_get(v_e_2270_, 1);
                                lean_inc_ref(v_expr_2306_);
                                v___x_2307_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_expr_2306_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2307_;
                                state = 2;
                                continue;
                            }
                            11 => {
                                v_struct_2308_ = lean_ctor_get(v_e_2270_, 2);
                                lean_inc_ref(v_struct_2308_);
                                v___x_2309_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2269_, v_struct_2308_, v_a_2271_, v___y_2272_);
                                v___y_2280_ = v___x_2309_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                lean_dec_ref(v_g_2269_);
                                v___x_2310_ = lean_box(0);
                                v_val_2275_ = v___x_2310_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_2270_);
                    lean_dec_ref(v_g_2269_);
                    v_val_2311_ = lean_ctor_get(v___x_2282_, 0);
                    lean_inc(v_val_2311_);
                    lean_dec_ref_known(v___x_2282_, 1);
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
                lean_inc_ref(v_g_2269_);
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
    mut v_g_2312_: *mut LeanObject,
    mut v_e_2313_: *mut LeanObject,
    mut v_a_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2317_: *mut LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2312_, v_e_2313_, v_a_2314_, v___y_2315_);
    lean_dec(v___y_2315_);
    lean_dec(v_a_2314_);
    return v_res_2317_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0()
-> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = lean_box(0);
    v___x_2319_ = lean_unsigned_to_nat(16);
    v___x_2320_ = lean_mk_array(v___x_2319_, v___x_2318_);
    return v___x_2320_;
}
pub unsafe fn _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    v___x_2321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__0);
    v___x_2322_ = lean_unsigned_to_nat(0);
    v___x_2323_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    lean_ctor_set(v___x_2323_, 1, v___x_2321_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2(
    mut v___f_2324_: *mut LeanObject,
    mut v_e_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    v___x_2328_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1_once), _init_l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___closed__1);
    v___x_2329_ = lean_st_mk_ref(v___x_2328_);
    v___x_2330_ = lean_st_mk_ref(v___x_2328_);
    v___x_2331_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v___f_2324_, v_e_2325_, v___x_2330_, v___x_2329_);
    v___x_2332_ = lean_st_ref_get(v___x_2330_);
    lean_dec(v___x_2330_);
    lean_dec(v___x_2332_);
    v___x_2333_ = lean_st_ref_get(v___x_2329_);
    lean_dec(v___x_2329_);
    return v___x_2333_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___boxed(
    mut v___f_2334_: *mut LeanObject,
    mut v_e_2335_: *mut LeanObject,
    mut v_x_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ =
        l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2(
            v___f_2334_,
            v_e_2335_,
            v_x_2336_,
        );
    return v_res_2338_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped(
    mut v_e_2339_: *mut LeanObject,
    mut v_nm_u2080_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    v___f_2341_ = lean_alloc_closure(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_2341_, 0, v_nm_u2080_2340_);
    v___f_2342_ = lean_alloc_closure(l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_2342_, 0, v___f_2341_);
    lean_closure_set(v___f_2342_, 1, v_e_2339_);
    v___x_2343_ = l_runST___redArg(v___f_2342_);
    return v___x_2343_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0(
    mut v_00_u03b2_2344_: *mut LeanObject,
    mut v_m_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_b_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0___redArg(v_m_2345_, v_a_2346_, v_b_2347_);
    return v___x_2348_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2(
    mut v_x_2349_: *mut LeanObject,
    mut v_g_2350_: *mut LeanObject,
    mut v_e_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___redArg(v_g_2350_, v_e_2351_, v_a_2352_, v___y_2353_);
    return v___x_2355_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2___boxed(
    mut v_x_2356_: *mut LeanObject,
    mut v_g_2357_: *mut LeanObject,
    mut v_e_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2362_: *mut LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2(v_x_2356_, v_g_2357_, v_e_2358_, v_a_2359_, v___y_2360_);
    lean_dec(v___y_2360_);
    lean_dec(v_a_2359_);
    return v_res_2362_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0(
    mut v_00_u03b2_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_x_2365_: *mut LeanObject,
) -> u8 {
    let mut v___x_2366_: u8 = 0;
    v___x_2366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___redArg(v_a_2364_, v_x_2365_);
    return v___x_2366_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0___boxed(
    mut v_00_u03b2_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_x_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2370_: u8 = 0;
    let mut v_r_2371_: *mut LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0(v_00_u03b2_2367_, v_a_2368_, v_x_2369_);
    lean_dec(v_x_2369_);
    lean_dec_ref(v_a_2368_);
    v_r_2371_ = lean_box((v_res_2370_) as usize);
    return v_r_2371_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1(
    mut v_00_u03b2_2372_: *mut LeanObject,
    mut v_data_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1___redArg(v_data_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5(
    mut v_00_u03b2_2375_: *mut LeanObject,
    mut v_m_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___redArg(v_m_2376_, v_a_2377_);
    return v___x_2378_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5___boxed(
    mut v_00_u03b2_2379_: *mut LeanObject,
    mut v_m_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5(v_00_u03b2_2379_, v_m_2380_, v_a_2381_);
    lean_dec_ref(v_a_2381_);
    lean_dec_ref(v_m_2380_);
    return v_res_2382_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6(
    mut v_00_u03b2_2383_: *mut LeanObject,
    mut v_m_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_b_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6___redArg(v_m_2384_, v_a_2385_, v_b_2386_);
    return v___x_2387_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1(
    mut v_xs_2388_: *mut LeanObject,
    mut v_ys_2389_: *mut LeanObject,
    mut v_hsz_2390_: *mut LeanObject,
    mut v_x_2391_: *mut LeanObject,
    mut v_x_2392_: *mut LeanObject,
) -> u8 {
    let mut v___x_2393_: u8 = 0;
    v___x_2393_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___redArg(v_xs_2388_, v_ys_2389_, v_x_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2394_: *mut LeanObject,
    mut v_ys_2395_: *mut LeanObject,
    mut v_hsz_2396_: *mut LeanObject,
    mut v_x_2397_: *mut LeanObject,
    mut v_x_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2399_: u8 = 0;
    let mut v_r_2400_: *mut LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__0_spec__1(v_xs_2394_, v_ys_2395_, v_hsz_2396_, v_x_2397_, v_x_2398_);
    lean_dec_ref(v_ys_2395_);
    lean_dec_ref(v_xs_2394_);
    v_r_2400_ = lean_box((v_res_2399_) as usize);
    return v_r_2400_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2401_: *mut LeanObject,
    mut v_i_2402_: *mut LeanObject,
    mut v_source_2403_: *mut LeanObject,
    mut v_target_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    v___x_2405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3___redArg(v_i_2402_, v_source_2403_, v_target_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8(
    mut v_00_u03b2_2406_: *mut LeanObject,
    mut v_a_2407_: *mut LeanObject,
    mut v_x_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___redArg(v_a_2407_, v_x_2408_);
    return v___x_2409_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b2_2410_: *mut LeanObject,
    mut v_a_2411_: *mut LeanObject,
    mut v_x_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__5_spec__8(v_00_u03b2_2410_, v_a_2411_, v_x_2412_);
    lean_dec(v_x_2412_);
    lean_dec_ref(v_a_2411_);
    return v_res_2413_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10(
    mut v_00_u03b2_2414_: *mut LeanObject,
    mut v_a_2415_: *mut LeanObject,
    mut v_x_2416_: *mut LeanObject,
) -> u8 {
    let mut v___x_2417_: u8 = 0;
    v___x_2417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___redArg(v_a_2415_, v_x_2416_);
    return v___x_2417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10___boxed(
    mut v_00_u03b2_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_x_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2421_: u8 = 0;
    let mut v_r_2422_: *mut LeanObject = core::ptr::null_mut();
    v_res_2421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__10(v_00_u03b2_2418_, v_a_2419_, v_x_2420_);
    lean_dec(v_x_2420_);
    lean_dec_ref(v_a_2419_);
    v_r_2422_ = lean_box((v_res_2421_) as usize);
    return v_r_2422_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11(
    mut v_00_u03b2_2423_: *mut LeanObject,
    mut v_data_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    v___x_2425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11___redArg(v_data_2424_);
    return v___x_2425_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12(
    mut v_00_u03b2_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
    mut v_b_2428_: *mut LeanObject,
    mut v_x_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__12___redArg(v_a_2427_, v_b_2428_, v_x_2429_);
    return v___x_2430_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_2431_: *mut LeanObject,
    mut v_x_2432_: *mut LeanObject,
    mut v_x_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2432_, v_x_2433_);
    return v___x_2434_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13(
    mut v_00_u03b2_2435_: *mut LeanObject,
    mut v_i_2436_: *mut LeanObject,
    mut v_source_2437_: *mut LeanObject,
    mut v_target_2438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13___redArg(v_i_2436_, v_source_2437_, v_target_2438_);
    return v___x_2439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14(
    mut v_00_u03b2_2440_: *mut LeanObject,
    mut v_x_2441_: *mut LeanObject,
    mut v_x_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__2_spec__6_spec__11_spec__13_spec__14___redArg(v_x_2441_, v_x_2442_);
    return v___x_2443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0(
    mut v_a_2444_: *mut LeanObject,
    mut v_as_2445_: *mut LeanObject,
    mut v_i_2446_: usize,
    mut v_stop_2447_: usize,
) -> u8 {
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2455_: *mut LeanObject,
    mut v_as_2456_: *mut LeanObject,
    mut v_i_2457_: *mut LeanObject,
    mut v_stop_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2459_: usize = 0;
    let mut v_stop_boxed_2460_: usize = 0;
    let mut v_res_2461_: u8 = 0;
    let mut v_r_2462_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2459_ = lean_unbox_usize(v_i_2457_);
    lean_dec(v_i_2457_);
    v_stop_boxed_2460_ = lean_unbox_usize(v_stop_2458_);
    lean_dec(v_stop_2458_);
    v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0_spec__0(v_a_2455_, v_as_2456_, v_i_boxed_2459_, v_stop_boxed_2460_);
    lean_dec_ref(v_as_2456_);
    lean_dec(v_a_2455_);
    v_r_2462_ = lean_box((v_res_2461_) as usize);
    return v_r_2462_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(
    mut v_as_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
) -> u8 {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    v___x_2465_ = lean_unsigned_to_nat(0);
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
    mut v_as_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: u8 = 0;
    let mut v_r_2474_: *mut LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_as_2471_, v_a_2472_);
    lean_dec(v_a_2472_);
    lean_dec_ref(v_as_2471_);
    v_r_2474_ = lean_box((v_res_2473_) as usize);
    return v_r_2474_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(
    mut v_goodLevels_2475_: *mut LeanObject,
    mut v_as_2476_: *mut LeanObject,
    mut v_i_2477_: usize,
    mut v_stop_2478_: usize,
    mut v_b_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: usize = 0;
    let mut v___x_2483_: usize = 0;
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: u8 = 0;
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2485_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
                if v___x_2485_ == 0 {
                    v___x_2486_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
                    v___x_2487_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_goodLevels_2475_, v___x_2486_);
                    if v___x_2487_ == 0 {
                        lean_inc(v___x_2486_);
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
    mut v_goodLevels_2489_: *mut LeanObject,
    mut v_as_2490_: *mut LeanObject,
    mut v_i_2491_: *mut LeanObject,
    mut v_stop_2492_: *mut LeanObject,
    mut v_b_2493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2494_: usize = 0;
    let mut v_stop_boxed_2495_: usize = 0;
    let mut v_res_2496_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2494_ = lean_unbox_usize(v_i_2491_);
    lean_dec(v_i_2491_);
    v_stop_boxed_2495_ = lean_unbox_usize(v_stop_2492_);
    lean_dec(v_stop_2492_);
    v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2489_, v_as_2490_, v_i_boxed_2494_, v_stop_boxed_2495_, v_b_2493_);
    lean_dec_ref(v_as_2490_);
    lean_dec_ref(v_goodLevels_2489_);
    return v_res_2496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(
    mut v_goodLevels_2497_: *mut LeanObject,
    mut v_sz_2498_: usize,
    mut v_i_2499_: usize,
    mut v_bs_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: usize = 0;
    let mut v___x_2508_: usize = 0;
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: usize = 0;
    let mut v___x_2516_: usize = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: usize = 0;
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_usize_dec_lt(v_i_2499_, v_sz_2498_);
                if v___x_2501_ == 0 {
                    return v_bs_2500_;
                } else {
                    v___x_2502_ = lean_unsigned_to_nat(0);
                    v_v_2503_ = lean_array_uget(v_bs_2500_, v_i_2499_);
                    v_bs_x27_2504_ = lean_array_uset(v_bs_2500_, v_i_2499_, v___x_2502_);
                    v___x_2511_ = lean_array_get_size(v_v_2503_);
                    v___x_2512_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
                    v___x_2513_ = lean_nat_dec_lt(v___x_2502_, v___x_2511_);
                    if v___x_2513_ == 0 {
                        lean_dec(v_v_2503_);
                        v___y_2506_ = v___x_2512_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2514_ = lean_nat_dec_le(v___x_2511_, v___x_2511_);
                        if v___x_2514_ == 0 {
                            if v___x_2513_ == 0 {
                                lean_dec(v_v_2503_);
                                v___y_2506_ = v___x_2512_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2515_ = 0usize;
                                v___x_2516_ = lean_usize_of_nat(v___x_2511_);
                                v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2497_, v_v_2503_, v___x_2515_, v___x_2516_, v___x_2512_);
                                lean_dec(v_v_2503_);
                                v___y_2506_ = v___x_2517_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2518_ = 0usize;
                            v___x_2519_ = lean_usize_of_nat(v___x_2511_);
                            v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__2(v_goodLevels_2497_, v_v_2503_, v___x_2518_, v___x_2519_, v___x_2512_);
                            lean_dec(v_v_2503_);
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
    mut v_goodLevels_2521_: *mut LeanObject,
    mut v_sz_2522_: *mut LeanObject,
    mut v_i_2523_: *mut LeanObject,
    mut v_bs_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2525_: usize = 0;
    let mut v_i_boxed_2526_: usize = 0;
    let mut v_res_2527_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2525_ = lean_unbox_usize(v_sz_2522_);
    lean_dec(v_sz_2522_);
    v_i_boxed_2526_ = lean_unbox_usize(v_i_2523_);
    lean_dec(v_i_2523_);
    v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(v_goodLevels_2521_, v_sz_boxed_2525_, v_i_boxed_2526_, v_bs_2524_);
    lean_dec_ref(v_goodLevels_2521_);
    return v_res_2527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(
    mut v_as_2528_: *mut LeanObject,
    mut v_i_2529_: usize,
    mut v_stop_2530_: usize,
    mut v_b_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_2538_: *mut LeanObject,
    mut v_i_2539_: *mut LeanObject,
    mut v_stop_2540_: *mut LeanObject,
    mut v_b_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2542_: usize = 0;
    let mut v_stop_boxed_2543_: usize = 0;
    let mut v_res_2544_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2542_ = lean_unbox_usize(v_i_2539_);
    lean_dec(v_i_2539_);
    v_stop_boxed_2543_ = lean_unbox_usize(v_stop_2540_);
    lean_dec(v_stop_2540_);
    v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_as_2538_, v_i_boxed_2542_, v_stop_boxed_2543_, v_b_2541_);
    lean_dec_ref(v_as_2538_);
    return v_res_2544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(
    mut v_as_2545_: *mut LeanObject,
    mut v_i_2546_: usize,
    mut v_stop_2547_: usize,
    mut v_b_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: usize = 0;
    let mut v___x_2552_: usize = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2554_ = lean_usize_dec_eq(v_i_2546_, v_stop_2547_);
                if v___x_2554_ == 0 {
                    v___x_2555_ = lean_array_uget_borrowed(v_as_2545_, v_i_2546_);
                    v___x_2556_ = l_Array_contains___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__0(v_b_2548_, v___x_2555_);
                    if v___x_2556_ == 0 {
                        lean_inc(v___x_2555_);
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
    mut v_as_2558_: *mut LeanObject,
    mut v_i_2559_: *mut LeanObject,
    mut v_stop_2560_: *mut LeanObject,
    mut v_b_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2562_: usize = 0;
    let mut v_stop_boxed_2563_: usize = 0;
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2562_ = lean_unbox_usize(v_i_2559_);
    lean_dec(v_i_2559_);
    v_stop_boxed_2563_ = lean_unbox_usize(v_stop_2560_);
    lean_dec(v_stop_2560_);
    v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v_as_2558_, v_i_boxed_2562_, v_stop_boxed_2563_, v_b_2561_);
    lean_dec_ref(v_as_2558_);
    return v_res_2564_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(
    mut v_as_2565_: *mut LeanObject,
    mut v_i_2566_: usize,
    mut v_stop_2567_: usize,
    mut v_b_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: u8 = 0;
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2574_ = lean_usize_dec_eq(v_i_2566_, v_stop_2567_);
                if v___x_2574_ == 0 {
                    v___x_2575_ = lean_array_uget_borrowed(v_as_2565_, v_i_2566_);
                    v___x_2576_ = lean_array_get_size(v___x_2575_);
                    v___x_2577_ = lean_unsigned_to_nat(1);
                    v___x_2578_ = lean_nat_dec_eq(v___x_2576_, v___x_2577_);
                    if v___x_2578_ == 0 {
                        v___y_2570_ = v_b_2568_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2579_ = lean_unsigned_to_nat(0);
                        v___x_2580_ = lean_array_fget_borrowed(v___x_2575_, v___x_2579_);
                        lean_inc(v___x_2580_);
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
    mut v_as_2582_: *mut LeanObject,
    mut v_i_2583_: *mut LeanObject,
    mut v_stop_2584_: *mut LeanObject,
    mut v_b_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2586_: usize = 0;
    let mut v_stop_boxed_2587_: usize = 0;
    let mut v_res_2588_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2586_ = lean_unbox_usize(v_i_2583_);
    lean_dec(v_i_2583_);
    v_stop_boxed_2587_ = lean_unbox_usize(v_stop_2584_);
    lean_dec(v_stop_2584_);
    v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2582_, v_i_boxed_2586_, v_stop_boxed_2587_, v_b_2585_);
    lean_dec_ref(v_as_2582_);
    return v_res_2588_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(
    mut v_as_2589_: *mut LeanObject,
    mut v_start_2590_: *mut LeanObject,
    mut v_stop_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    v___x_2592_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
    v___x_2593_ = lean_nat_dec_lt(v_start_2590_, v_stop_2591_);
    if v___x_2593_ == 0 {
        return v___x_2592_;
    } else {
        let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
                v___x_2597_ = lean_usize_of_nat(v_start_2590_);
                v___x_2598_ = lean_usize_of_nat(v___x_2594_);
                v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2589_, v___x_2597_, v___x_2598_, v___x_2592_);
                return v___x_2599_;
            }
        } else {
            let mut v___x_2600_: usize = 0;
            let mut v___x_2601_: usize = 0;
            let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
            v___x_2600_ = lean_usize_of_nat(v_start_2590_);
            v___x_2601_ = lean_usize_of_nat(v_stop_2591_);
            v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1_spec__2(v_as_2589_, v___x_2600_, v___x_2601_, v___x_2592_);
            return v___x_2602_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1___boxed(
    mut v_as_2603_: *mut LeanObject,
    mut v_start_2604_: *mut LeanObject,
    mut v_stop_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2606_: *mut LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(v_as_2603_, v_start_2604_, v_stop_2605_);
    lean_dec(v_stop_2605_);
    lean_dec(v_start_2604_);
    lean_dec_ref(v_as_2603_);
    return v_res_2606_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams(
    mut v_l_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goodLevels_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v_sz_2615_: usize = 0;
    let mut v___x_2616_: usize = 0;
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: usize = 0;
    let mut v___x_2626_: usize = 0;
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: usize = 0;
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: usize = 0;
    let mut v___x_2635_: usize = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: usize = 0;
    let mut v___x_2638_: usize = 0;
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = lean_unsigned_to_nat(0);
                v___x_2611_ = lean_array_get_size(v_l_2609_);
                v_goodLevels_2612_ = l_Array_filterMapM___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__1(v_l_2609_, v___x_2610_, v___x_2611_);
                v___x_2613_ = lean_array_get_size(v_goodLevels_2612_);
                v___x_2614_ = lean_nat_dec_eq(v___x_2613_, v___x_2610_);
                if v___x_2614_ == 0 {
                    v_sz_2615_ = lean_array_size(v_l_2609_);
                    v___x_2616_ = 0usize;
                    v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__3(v_goodLevels_2612_, v_sz_2615_, v___x_2616_, v_l_2609_);
                    lean_dec_ref(v_goodLevels_2612_);
                    v_l_2609_ = v___x_2617_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_goodLevels_2612_);
                    v___x_2619_ = l_List_foldl___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped_spec__1___closed__2;
                    v___x_2631_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams___closed__0;
                    v___x_2632_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
                    if v___x_2632_ == 0 {
                        lean_dec_ref(v_l_2609_);
                        v___y_2621_ = v___x_2631_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2633_ = lean_nat_dec_le(v___x_2611_, v___x_2611_);
                        if v___x_2633_ == 0 {
                            if v___x_2632_ == 0 {
                                lean_dec_ref(v_l_2609_);
                                v___y_2621_ = v___x_2631_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2634_ = 0usize;
                                v___x_2635_ = lean_usize_of_nat(v___x_2611_);
                                v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_l_2609_, v___x_2634_, v___x_2635_, v___x_2631_);
                                lean_dec_ref(v_l_2609_);
                                v___y_2621_ = v___x_2636_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2637_ = 0usize;
                            v___x_2638_ = lean_usize_of_nat(v___x_2611_);
                            v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__5(v_l_2609_, v___x_2637_, v___x_2638_, v___x_2631_);
                            lean_dec_ref(v_l_2609_);
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
                    lean_dec_ref(v___y_2621_);
                    return v___x_2619_;
                } else {
                    v___x_2624_ = lean_nat_dec_le(v___x_2622_, v___x_2622_);
                    if v___x_2624_ == 0 {
                        if v___x_2623_ == 0 {
                            lean_dec_ref(v___y_2621_);
                            return v___x_2619_;
                        } else {
                            v___x_2625_ = 0usize;
                            v___x_2626_ = lean_usize_of_nat(v___x_2622_);
                            v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v___y_2621_, v___x_2625_, v___x_2626_, v___x_2619_);
                            lean_dec_ref(v___y_2621_);
                            return v___x_2627_;
                        }
                    } else {
                        v___x_2628_ = 0usize;
                        v___x_2629_ = lean_usize_of_nat(v___x_2622_);
                        v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_badParams_spec__4(v___y_2621_, v___x_2628_, v___x_2629_, v___x_2619_);
                        lean_dec_ref(v___y_2621_);
                        return v___x_2630_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
    mut v___y_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = lean_st_ref_get(v___y_2640_);
    v_infoState_2643_ = lean_ctor_get(v___x_2642_, 8);
    lean_inc_ref(v_infoState_2643_);
    lean_dec(v___x_2642_);
    v_trees_2644_ = lean_ctor_get(v_infoState_2643_, 2);
    lean_inc_ref(v_trees_2644_);
    lean_dec_ref(v_infoState_2643_);
    v___x_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2645_, 0, v_trees_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg___boxed(
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2648_: *mut LeanObject = core::ptr::null_mut();
    v_res_2648_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
            v___y_2646_,
        );
    lean_dec(v___y_2646_);
    return v_res_2648_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1(
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(
            v___y_2650_,
        );
    return v___x_2652_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___boxed(
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2656_: *mut LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1(
        v___y_2653_,
        v___y_2654_,
    );
    lean_dec(v___y_2654_);
    lean_dec_ref(v___y_2653_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(
    mut v_o_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2660_ = lean_st_ref_get(v___y_2658_);
    v_env_2661_ = lean_ctor_get(v___x_2660_, 0);
    lean_inc_ref(v_env_2661_);
    lean_dec(v___x_2660_);
    v___x_2662_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2663_ = lean_ctor_get(v___x_2662_, 0);
    v_asyncMode_2664_ = lean_ctor_get(v_toEnvExtension_2663_, 2);
    v___x_2665_ = lean_box(1);
    v___x_2666_ = lean_box(0);
    v_linterSets_2667_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2665_,
        v___x_2662_,
        v_env_2661_,
        v_asyncMode_2664_,
        v___x_2666_,
    );
    v___x_2668_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2668_, 0, v_o_2657_);
    lean_ctor_set(v___x_2668_, 1, v_linterSets_2667_);
    v___x_2669_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2669_, 0, v___x_2668_);
    return v___x_2669_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg___boxed(
    mut v_o_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_o_2670_, v___y_2671_);
    lean_dec(v___y_2671_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2677_ = lean_st_ref_get(v___y_2675_);
    v_scopes_2678_ = lean_ctor_get(v___x_2677_, 2);
    lean_inc(v_scopes_2678_);
    lean_dec(v___x_2677_);
    v___x_2679_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2680_ = l_List_head_x21___redArg(v___x_2679_, v_scopes_2678_);
    lean_dec(v_scopes_2678_);
    v_opts_2681_ = lean_ctor_get(v___x_2680_, 1);
    lean_inc_ref(v_opts_2681_);
    lean_dec(v___x_2680_);
    v___x_2682_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_opts_2681_, v___y_2675_);
    return v___x_2682_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0___boxed(
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2686_: *mut LeanObject = core::ptr::null_mut();
    v_res_2686_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(
            v___y_2683_,
            v___y_2684_,
        );
    lean_dec(v___y_2684_);
    lean_dec_ref(v___y_2683_);
    return v_res_2686_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    v___x_2687_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2688_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__0);
    v___x_2689_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2689_, 0, v___x_2688_);
    return v___x_2689_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    v___x_2690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1);
    v___x_2691_ = lean_unsigned_to_nat(0);
    v___x_2692_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2692_, 0, v___x_2691_);
    lean_ctor_set(v___x_2692_, 1, v___x_2691_);
    lean_ctor_set(v___x_2692_, 2, v___x_2691_);
    lean_ctor_set(v___x_2692_, 3, v___x_2691_);
    lean_ctor_set(v___x_2692_, 4, v___x_2690_);
    lean_ctor_set(v___x_2692_, 5, v___x_2690_);
    lean_ctor_set(v___x_2692_, 6, v___x_2690_);
    lean_ctor_set(v___x_2692_, 7, v___x_2690_);
    lean_ctor_set(v___x_2692_, 8, v___x_2690_);
    lean_ctor_set(v___x_2692_, 9, v___x_2690_);
    return v___x_2692_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    v___x_2693_ = lean_unsigned_to_nat(32);
    v___x_2694_ = lean_mk_empty_array_with_capacity(v___x_2693_);
    v___x_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2695_, 0, v___x_2694_);
    return v___x_2695_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    v___x_2696_ = 5usize;
    v___x_2697_ = lean_unsigned_to_nat(0);
    v___x_2698_ = lean_unsigned_to_nat(32);
    v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2698_);
    v___x_2700_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__3);
    v___x_2701_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2701_, 0, v___x_2700_);
    lean_ctor_set(v___x_2701_, 1, v___x_2699_);
    lean_ctor_set(v___x_2701_, 2, v___x_2697_);
    lean_ctor_set(v___x_2701_, 3, v___x_2697_);
    lean_ctor_set_usize(v___x_2701_, 4, v___x_2696_);
    return v___x_2701_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    v___x_2702_ = lean_box(1);
    v___x_2703_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__4);
    v___x_2704_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__1);
    v___x_2705_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2705_, 0, v___x_2704_);
    lean_ctor_set(v___x_2705_, 1, v___x_2703_);
    lean_ctor_set(v___x_2705_, 2, v___x_2702_);
    return v___x_2705_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(
    mut v_msgData_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    v___x_2709_ = lean_st_ref_get(v___y_2707_);
    v_env_2710_ = lean_ctor_get(v___x_2709_, 0);
    lean_inc_ref(v_env_2710_);
    lean_dec(v___x_2709_);
    v___x_2711_ = lean_st_ref_get(v___y_2707_);
    v_scopes_2712_ = lean_ctor_get(v___x_2711_, 2);
    lean_inc(v_scopes_2712_);
    lean_dec(v___x_2711_);
    v___x_2713_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2714_ = l_List_head_x21___redArg(v___x_2713_, v_scopes_2712_);
    lean_dec(v_scopes_2712_);
    v_opts_2715_ = lean_ctor_get(v___x_2714_, 1);
    lean_inc_ref(v_opts_2715_);
    lean_dec(v___x_2714_);
    v___x_2716_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__2);
    v___x_2717_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___closed__5);
    v___x_2718_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2718_, 0, v_env_2710_);
    lean_ctor_set(v___x_2718_, 1, v___x_2716_);
    lean_ctor_set(v___x_2718_, 2, v___x_2717_);
    lean_ctor_set(v___x_2718_, 3, v_opts_2715_);
    v___x_2719_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2719_, 0, v___x_2718_);
    lean_ctor_set(v___x_2719_, 1, v_msgData_2706_);
    v___x_2720_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2720_, 0, v___x_2719_);
    return v___x_2720_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg___boxed(
    mut v_msgData_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v_msgData_2721_, v___y_2722_);
    lean_dec(v___y_2722_);
    return v_res_2724_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0(
    mut v___y_2726_: u8,
    mut v_suppressElabErrors_2727_: u8,
    mut v_x_2728_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2728_) == 1 {
        let mut v_pre_2729_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2729_ = lean_ctor_get(v_x_2728_, 0);
        if lean_obj_tag(v_pre_2729_) == 0 {
            let mut v_str_2730_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2732_: u8 = 0;
            v_str_2730_ = lean_ctor_get(v_x_2728_, 1);
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
    mut v___y_2733_: *mut LeanObject,
    mut v_suppressElabErrors_2734_: *mut LeanObject,
    mut v_x_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10221__boxed_2736_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2737_: u8 = 0;
    let mut v_res_2738_: u8 = 0;
    let mut v_r_2739_: *mut LeanObject = core::ptr::null_mut();
    v___y_10221__boxed_2736_ = (lean_unbox(v___y_2733_) as u8);
    v_suppressElabErrors_boxed_2737_ = (lean_unbox(v_suppressElabErrors_2734_) as u8);
    v_res_2738_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0(v___y_10221__boxed_2736_, v_suppressElabErrors_boxed_2737_, v_x_2735_);
    lean_dec(v_x_2735_);
    v_r_2739_ = lean_box((v_res_2738_) as usize);
    return v_r_2739_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(
    mut v_opts_2740_: *mut LeanObject,
    mut v_opt_2741_: *mut LeanObject,
) -> u8 {
    let mut v_name_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v_name_2742_ = lean_ctor_get(v_opt_2741_, 0);
    v_defValue_2743_ = lean_ctor_get(v_opt_2741_, 1);
    v_map_2744_ = lean_ctor_get(v_opts_2740_, 0);
    v___x_2745_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2744_,
            v_name_2742_,
        );
    if lean_obj_tag(v___x_2745_) == 0 {
        let mut v___x_2746_: u8 = 0;
        v___x_2746_ = (lean_unbox(v_defValue_2743_) as u8);
        return v___x_2746_;
    } else {
        let mut v_val_2747_: *mut LeanObject = core::ptr::null_mut();
        v_val_2747_ = lean_ctor_get(v___x_2745_, 0);
        lean_inc(v_val_2747_);
        lean_dec_ref_known(v___x_2745_, 1);
        if lean_obj_tag(v_val_2747_) == 1 {
            let mut v_v_2748_: u8 = 0;
            v_v_2748_ = lean_ctor_get_uint8(v_val_2747_, 0 as u32);
            lean_dec_ref_known(v_val_2747_, 0);
            return v_v_2748_;
        } else {
            let mut v___x_2749_: u8 = 0;
            lean_dec(v_val_2747_);
            v___x_2749_ = (lean_unbox(v_defValue_2743_) as u8);
            return v___x_2749_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14___boxed(
    mut v_opts_2750_: *mut LeanObject,
    mut v_opt_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2752_: u8 = 0;
    let mut v_r_2753_: *mut LeanObject = core::ptr::null_mut();
    v_res_2752_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(v_opts_2750_, v_opt_2751_);
    lean_dec_ref(v_opt_2751_);
    lean_dec_ref(v_opts_2750_);
    v_r_2753_ = lean_box((v_res_2752_) as usize);
    return v_r_2753_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(
    mut v_ref_2755_: *mut LeanObject,
    mut v_msgData_2756_: *mut LeanObject,
    mut v_severity_2757_: u8,
    mut v_isSilent_2758_: u8,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2763_: u8 = 0;
    let mut v___y_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: u8 = 0;
    let mut v___y_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2824_: u8 = 0;
    let mut v___y_2826_: u8 = 0;
    let mut v___y_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: u8 = 0;
    let mut v___y_2829_: u8 = 0;
    let mut v___y_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2833_: u8 = 0;
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v___y_2854_: u8 = 0;
    let mut v___y_2855_: u8 = 0;
    let mut v___y_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2857_: u8 = 0;
    let mut v___y_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: u8 = 0;
    let mut v___y_2863_: u8 = 0;
    let mut v___y_2864_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___y_2881_: u8 = 0;
    let mut v___y_2882_: u8 = 0;
    let mut v___y_2883_: u8 = 0;
    let mut v___y_2885_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: u8 = 0;
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_2756_);
                    v___x_2898_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2756_);
                    v___y_2885_ = v___x_2898_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2771_ = l_Lean_Elab_Command_getScope___redArg(v___y_2770_);
                if lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
                    lean_inc(v_a_2772_);
                    lean_dec_ref_known(v___x_2771_, 1);
                    v___x_2773_ = l_Lean_Elab_Command_getScope___redArg(v___y_2770_);
                    if lean_obj_tag(v___x_2773_) == 0 {
                        v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
                        v_isSharedCheck_2808_ = (!lean_is_exclusive(v___x_2773_)) as u8;
                        if v_isSharedCheck_2808_ == 0 {
                            v___x_2776_ = v___x_2773_;
                            v_isShared_2777_ = v_isSharedCheck_2808_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2774_);
                            lean_dec(v___x_2773_);
                            v___x_2776_ = lean_box(0);
                            v_isShared_2777_ = v_isSharedCheck_2808_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2772_);
                        lean_dec_ref(v___y_2767_);
                        lean_dec(v___y_2766_);
                        lean_dec_ref(v___y_2764_);
                        v_a_2809_ = lean_ctor_get(v___x_2773_, 0);
                        v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2773_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v___x_2811_ = v___x_2773_;
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2809_);
                            lean_dec(v___x_2773_);
                            v___x_2811_ = lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2767_);
                    lean_dec(v___y_2766_);
                    lean_dec_ref(v___y_2764_);
                    v_a_2817_ = lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2824_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2824_ == 0 {
                        v___x_2819_ = v___x_2771_;
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2817_);
                        lean_dec(v___x_2771_);
                        v___x_2819_ = lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2778_ = lean_st_ref_take(v___y_2770_);
                v_currNamespace_2779_ = lean_ctor_get(v_a_2772_, 2);
                lean_inc(v_currNamespace_2779_);
                lean_dec(v_a_2772_);
                v_openDecls_2780_ = lean_ctor_get(v_a_2774_, 3);
                lean_inc(v_openDecls_2780_);
                lean_dec(v_a_2774_);
                v_env_2781_ = lean_ctor_get(v___x_2778_, 0);
                v_messages_2782_ = lean_ctor_get(v___x_2778_, 1);
                v_scopes_2783_ = lean_ctor_get(v___x_2778_, 2);
                v_usedQuotCtxts_2784_ = lean_ctor_get(v___x_2778_, 3);
                v_nextMacroScope_2785_ = lean_ctor_get(v___x_2778_, 4);
                v_maxRecDepth_2786_ = lean_ctor_get(v___x_2778_, 5);
                v_ngen_2787_ = lean_ctor_get(v___x_2778_, 6);
                v_auxDeclNGen_2788_ = lean_ctor_get(v___x_2778_, 7);
                v_infoState_2789_ = lean_ctor_get(v___x_2778_, 8);
                v_traceState_2790_ = lean_ctor_get(v___x_2778_, 9);
                v_snapshotTasks_2791_ = lean_ctor_get(v___x_2778_, 10);
                v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2778_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2793_ = v___x_2778_;
                    v_isShared_2794_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2791_);
                    lean_inc(v_traceState_2790_);
                    lean_inc(v_infoState_2789_);
                    lean_inc(v_auxDeclNGen_2788_);
                    lean_inc(v_ngen_2787_);
                    lean_inc(v_maxRecDepth_2786_);
                    lean_inc(v_nextMacroScope_2785_);
                    lean_inc(v_usedQuotCtxts_2784_);
                    lean_inc(v_scopes_2783_);
                    lean_inc(v_messages_2782_);
                    lean_inc(v_env_2781_);
                    lean_dec(v___x_2778_);
                    v___x_2793_ = lean_box(0);
                    v_isShared_2794_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2795_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2795_, 0, v_currNamespace_2779_);
                lean_ctor_set(v___x_2795_, 1, v_openDecls_2780_);
                v___x_2796_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                lean_ctor_set(v___x_2796_, 1, v___y_2767_);
                lean_inc_ref(v___y_2769_);
                lean_inc_ref(v___y_2765_);
                v___x_2797_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2797_, 0, v___y_2765_);
                lean_ctor_set(v___x_2797_, 1, v___y_2764_);
                lean_ctor_set(v___x_2797_, 2, v___y_2766_);
                lean_ctor_set(v___x_2797_, 3, v___y_2769_);
                lean_ctor_set(v___x_2797_, 4, v___x_2796_);
                lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2763_,
                );
                lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2768_,
                );
                lean_ctor_set_uint8(
                    v___x_2797_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2758_,
                );
                v___x_2798_ = l_Lean_MessageLog_add(v___x_2797_, v_messages_2782_);
                if v_isShared_2794_ == 0 {
                    lean_ctor_set(v___x_2793_, 1, v___x_2798_);
                    v___x_2800_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_env_2781_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_scopes_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_usedQuotCtxts_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_nextMacroScope_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 5, v_maxRecDepth_2786_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 6, v_ngen_2787_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 7, v_auxDeclNGen_2788_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 8, v_infoState_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 9, v_traceState_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 10, v_snapshotTasks_2791_);
                    v___x_2800_ = v_reuseFailAlloc_2806_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2801_ = lean_st_ref_set(v___y_2770_, v___x_2800_);
                v___x_2802_ = lean_box(0);
                if v_isShared_2777_ == 0 {
                    lean_ctor_set(v___x_2776_, 0, v___x_2802_);
                    v___x_2804_ = v___x_2776_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
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
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
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
                    v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
                    v___x_2822_ = v_reuseFailAlloc_2823_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2822_;
            }
            10 => {
                v_fileName_2831_ = lean_ctor_get(v___y_2759_, 0);
                v_fileMap_2832_ = lean_ctor_get(v___y_2759_, 1);
                v_suppressElabErrors_2833_ = lean_ctor_get_uint8(
                    v___y_2759_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_2834_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2756_,
                    );
                v___x_2835_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v___x_2834_, v___y_2760_);
                v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
                v_isSharedCheck_2852_ = (!lean_is_exclusive(v___x_2835_)) as u8;
                if v_isSharedCheck_2852_ == 0 {
                    v___x_2838_ = v___x_2835_;
                    v_isShared_2839_ = v_isSharedCheck_2852_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_2836_);
                    lean_dec(v___x_2835_);
                    v___x_2838_ = lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2852_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_2832_, 2);
                v___x_2840_ = l_Lean_FileMap_toPosition(v_fileMap_2832_, v___y_2827_);
                lean_dec(v___y_2827_);
                v___x_2841_ = l_Lean_FileMap_toPosition(v_fileMap_2832_, v___y_2830_);
                lean_dec(v___y_2830_);
                v___x_2842_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                v___x_2843_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___closed__0;
                if v_suppressElabErrors_2833_ == 0 {
                    lean_del_object(v___x_2838_);
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
                    v___x_2844_ = lean_box((v___y_2826_) as usize);
                    v___x_2845_ = lean_box((v_suppressElabErrors_2833_) as usize);
                    v___f_2846_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2846_, 0, v___x_2844_);
                    lean_closure_set(v___f_2846_, 1, v___x_2845_);
                    lean_inc(v_a_2836_);
                    v___x_2847_ = l_Lean_MessageData_hasTag(v___f_2846_, v_a_2836_);
                    if v___x_2847_ == 0 {
                        lean_dec_ref_known(v___x_2842_, 1);
                        lean_dec_ref(v___x_2840_);
                        lean_dec(v_a_2836_);
                        v___x_2848_ = lean_box(0);
                        if v_isShared_2839_ == 0 {
                            lean_ctor_set(v___x_2838_, 0, v___x_2848_);
                            v___x_2850_ = v___x_2838_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
                            v___x_2850_ = v_reuseFailAlloc_2851_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2838_);
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
                lean_dec(v___y_2856_);
                if lean_obj_tag(v___x_2859_) == 0 {
                    lean_inc(v___y_2858_);
                    v___y_2826_ = v___y_2854_;
                    v___y_2827_ = v___y_2858_;
                    v___y_2828_ = v___y_2855_;
                    v___y_2829_ = v___y_2857_;
                    v___y_2830_ = v___y_2858_;
                    state = 10;
                    continue;
                } else {
                    v_val_2860_ = lean_ctor_get(v___x_2859_, 0);
                    lean_inc(v_val_2860_);
                    lean_dec_ref_known(v___x_2859_, 1);
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
                if lean_obj_tag(v___x_2865_) == 0 {
                    v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
                    lean_inc(v_a_2866_);
                    lean_dec_ref_known(v___x_2865_, 1);
                    v_ref_2867_ = l_Lean_replaceRef(v_ref_2755_, v_a_2866_);
                    lean_dec(v_a_2866_);
                    v___x_2868_ = l_Lean_Syntax_getPos_x3f(v_ref_2867_, v___y_2863_);
                    if lean_obj_tag(v___x_2868_) == 0 {
                        v___x_2869_ = lean_unsigned_to_nat(0);
                        v___y_2854_ = v___y_2862_;
                        v___y_2855_ = v___y_2863_;
                        v___y_2856_ = v_ref_2867_;
                        v___y_2857_ = v___y_2864_;
                        v___y_2858_ = v___x_2869_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2870_ = lean_ctor_get(v___x_2868_, 0);
                        lean_inc(v_val_2870_);
                        lean_dec_ref_known(v___x_2868_, 1);
                        v___y_2854_ = v___y_2862_;
                        v___y_2855_ = v___y_2863_;
                        v___y_2856_ = v_ref_2867_;
                        v___y_2857_ = v___y_2864_;
                        v___y_2858_ = v_val_2870_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_2756_);
                    v_a_2871_ = lean_ctor_get(v___x_2865_, 0);
                    v_isSharedCheck_2878_ = (!lean_is_exclusive(v___x_2865_)) as u8;
                    if v_isSharedCheck_2878_ == 0 {
                        v___x_2873_ = v___x_2865_;
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2871_);
                        lean_dec(v___x_2865_);
                        v___x_2873_ = lean_box(0);
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
                    v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
                    v_scopes_2887_ = lean_ctor_get(v___x_2886_, 2);
                    lean_inc(v_scopes_2887_);
                    lean_dec(v___x_2886_);
                    v___x_2888_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2889_ = l_List_head_x21___redArg(v___x_2888_, v_scopes_2887_);
                    lean_dec(v_scopes_2887_);
                    v_opts_2890_ = lean_ctor_get(v___x_2889_, 1);
                    lean_inc_ref(v_opts_2890_);
                    lean_dec(v___x_2889_);
                    v___x_2891_ = 1;
                    v___x_2892_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2757_, v___x_2891_);
                    if v___x_2892_ == 0 {
                        lean_dec_ref(v_opts_2890_);
                        v___y_2881_ = v___y_2885_;
                        v___y_2882_ = v___y_2885_;
                        v___y_2883_ = v___x_2892_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2893_ = l_Lean_warningAsError;
                        v___x_2894_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__14(v_opts_2890_, v___x_2893_);
                        lean_dec_ref(v_opts_2890_);
                        v___y_2881_ = v___y_2885_;
                        v___y_2882_ = v___y_2885_;
                        v___y_2883_ = v___x_2894_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_2756_);
                    v___x_2895_ = lean_box(0);
                    v___x_2896_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2896_, 0, v___x_2895_);
                    return v___x_2896_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10___boxed(
    mut v_ref_2899_: *mut LeanObject,
    mut v_msgData_2900_: *mut LeanObject,
    mut v_severity_2901_: *mut LeanObject,
    mut v_isSilent_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2906_: u8 = 0;
    let mut v_isSilent_boxed_2907_: u8 = 0;
    let mut v_res_2908_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2906_ = (lean_unbox(v_severity_2901_) as u8);
    v_isSilent_boxed_2907_ = (lean_unbox(v_isSilent_2902_) as u8);
    v_res_2908_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(v_ref_2899_, v_msgData_2900_, v_severity_boxed_2906_, v_isSilent_boxed_2907_, v___y_2903_, v___y_2904_);
    lean_dec(v___y_2904_);
    lean_dec_ref(v___y_2903_);
    lean_dec(v_ref_2899_);
    return v_res_2908_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(
    mut v_ref_2909_: *mut LeanObject,
    mut v_msgData_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = 1;
    v___x_2915_ = 0;
    v___x_2916_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10(v_ref_2909_, v_msgData_2910_, v___x_2914_, v___x_2915_, v___y_2911_, v___y_2912_);
    return v___x_2916_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5___boxed(
    mut v_ref_2917_: *mut LeanObject,
    mut v_msgData_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2922_: *mut LeanObject = core::ptr::null_mut();
    v_res_2922_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(v_ref_2917_, v_msgData_2918_, v___y_2919_, v___y_2920_);
    lean_dec(v___y_2920_);
    lean_dec_ref(v___y_2919_);
    lean_dec(v_ref_2917_);
    return v_res_2922_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__0;
    v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
    return v___x_2925_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    v___x_2927_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__2;
    v___x_2928_ = l_Lean_stringToMessageData(v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4(
    mut v_linterOption_2929_: *mut LeanObject,
    mut v_stx_2930_: *mut LeanObject,
    mut v_msg_2931_: *mut LeanObject,
    mut v___y_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v_unused_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2935_ = lean_ctor_get(v_linterOption_2929_, 0);
                v_isSharedCheck_2952_ = (!lean_is_exclusive(v_linterOption_2929_)) as u8;
                if v_isSharedCheck_2952_ == 0 {
                    v_unused_2953_ = lean_ctor_get(v_linterOption_2929_, 1);
                    lean_dec(v_unused_2953_);
                    v___x_2937_ = v_linterOption_2929_;
                    v_isShared_2938_ = v_isSharedCheck_2952_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2935_);
                    lean_dec(v_linterOption_2929_);
                    v___x_2937_ = lean_box(0);
                    v_isShared_2938_ = v_isSharedCheck_2952_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2939_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__1);
                lean_inc(v_name_2935_);
                v___x_2940_ = l_Lean_MessageData_ofName(v_name_2935_);
                if v_isShared_2938_ == 0 {
                    lean_ctor_set_tag(v___x_2937_, 7);
                    lean_ctor_set(v___x_2937_, 1, v___x_2940_);
                    lean_ctor_set(v___x_2937_, 0, v___x_2939_);
                    v___x_2942_ = v___x_2937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2939_);
                    lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2940_);
                    v___x_2942_ = v_reuseFailAlloc_2951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2943_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___closed__3);
                v___x_2944_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___x_2942_);
                lean_ctor_set(v___x_2944_, 1, v___x_2943_);
                v_disable_2945_ = l_Lean_MessageData_note(v___x_2944_);
                v___x_2946_ = l_Lean_Linter_linterMessageTag;
                v___x_2947_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2947_, 0, v_msg_2931_);
                lean_ctor_set(v___x_2947_, 1, v_disable_2945_);
                v___x_2948_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2948_, 0, v___x_2946_);
                lean_ctor_set(v___x_2948_, 1, v___x_2947_);
                v___x_2949_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2949_, 0, v_name_2935_);
                lean_ctor_set(v___x_2949_, 1, v___x_2948_);
                v___x_2950_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5(v_stx_2930_, v___x_2949_, v___y_2932_, v___y_2933_);
                return v___x_2950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4___boxed(
    mut v_linterOption_2954_: *mut LeanObject,
    mut v_stx_2955_: *mut LeanObject,
    mut v_msg_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2960_: *mut LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4(v_linterOption_2954_, v_stx_2955_, v_msg_2956_, v___y_2957_, v___y_2958_);
    lean_dec(v___y_2958_);
    lean_dec_ref(v___y_2957_);
    lean_dec(v_stx_2955_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(
    mut v_linterOption_2961_: *mut LeanObject,
    mut v_stx_2962_: *mut LeanObject,
    mut v_msg_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2971_: u8 = 0;
    let mut v___x_2972_: u8 = 0;
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2967_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(v___y_2964_, v___y_2965_);
                v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
                v_isSharedCheck_2978_ = (!lean_is_exclusive(v___x_2967_)) as u8;
                if v_isSharedCheck_2978_ == 0 {
                    v___x_2970_ = v___x_2967_;
                    v_isShared_2971_ = v_isSharedCheck_2978_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2968_);
                    lean_dec(v___x_2967_);
                    v___x_2970_ = lean_box(0);
                    v_isShared_2971_ = v_isSharedCheck_2978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2972_ = l_Lean_Linter_getLinterValue(v_linterOption_2961_, v_a_2968_);
                lean_dec(v_a_2968_);
                if v___x_2972_ == 0 {
                    lean_dec_ref(v_msg_2963_);
                    lean_dec_ref(v_linterOption_2961_);
                    v___x_2973_ = lean_box(0);
                    if v_isShared_2971_ == 0 {
                        lean_ctor_set(v___x_2970_, 0, v___x_2973_);
                        v___x_2975_ = v___x_2970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
                        v___x_2975_ = v_reuseFailAlloc_2976_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2970_);
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
    mut v_linterOption_2979_: *mut LeanObject,
    mut v_stx_2980_: *mut LeanObject,
    mut v_msg_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2985_: *mut LeanObject = core::ptr::null_mut();
    v_res_2985_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(
        v_linterOption_2979_,
        v_stx_2980_,
        v_msg_2981_,
        v___y_2982_,
        v___y_2983_,
    );
    lean_dec(v___y_2983_);
    lean_dec_ref(v___y_2982_);
    lean_dec(v_stx_2980_);
    return v_res_2985_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    v___x_2987_ =
        l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__0;
    v___x_2988_ = l_Lean_stringToMessageData(v___x_2987_);
    return v___x_2988_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2(
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2989_) == 0 {
                    v___x_2991_ = l_List_reverse___redArg(v_a_2990_);
                    return v___x_2991_;
                } else {
                    v_head_2992_ = lean_ctor_get(v_a_2989_, 0);
                    v_tail_2993_ = lean_ctor_get(v_a_2989_, 1);
                    v_isSharedCheck_3005_ = (!lean_is_exclusive(v_a_2989_)) as u8;
                    if v_isSharedCheck_3005_ == 0 {
                        v___x_2995_ = v_a_2989_;
                        v_isShared_2996_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2993_);
                        lean_inc(v_head_2992_);
                        lean_dec(v_a_2989_);
                        v___x_2995_ = lean_box(0);
                        v_isShared_2996_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2997_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1);
                v___x_2998_ = l_Lean_MessageData_ofName(v_head_2992_);
                v___x_2999_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2999_, 0, v___x_2997_);
                lean_ctor_set(v___x_2999_, 1, v___x_2998_);
                v___x_3000_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3000_, 0, v___x_2999_);
                lean_ctor_set(v___x_3000_, 1, v___x_2997_);
                if v_isShared_2996_ == 0 {
                    lean_ctor_set(v___x_2995_, 1, v_a_2990_);
                    lean_ctor_set(v___x_2995_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_a_2990_);
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
    mut v_x_3006_: *mut LeanObject,
    mut v_x_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3007_) == 0 {
                    return v_x_3006_;
                } else {
                    v_key_3008_ = lean_ctor_get(v_x_3007_, 0);
                    lean_inc(v_key_3008_);
                    v_tail_3009_ = lean_ctor_get(v_x_3007_, 2);
                    lean_inc(v_tail_3009_);
                    lean_dec_ref_known(v_x_3007_, 3);
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
    mut v_as_3012_: *mut LeanObject,
    mut v_i_3013_: usize,
    mut v_stop_3014_: usize,
    mut v_b_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: usize = 0;
    let mut v___x_3020_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3016_ = lean_usize_dec_eq(v_i_3013_, v_stop_3014_);
                if v___x_3016_ == 0 {
                    v___x_3017_ = lean_array_uget_borrowed(v_as_3012_, v_i_3013_);
                    lean_inc(v___x_3017_);
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
    mut v_as_3022_: *mut LeanObject,
    mut v_i_3023_: *mut LeanObject,
    mut v_stop_3024_: *mut LeanObject,
    mut v_b_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3026_: usize = 0;
    let mut v_stop_boxed_3027_: usize = 0;
    let mut v_res_3028_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3026_ = lean_unbox_usize(v_i_3023_);
    lean_dec(v_i_3023_);
    v_stop_boxed_3027_ = lean_unbox_usize(v_stop_3024_);
    lean_dec(v_stop_3024_);
    v_res_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_as_3022_, v_i_boxed_3026_, v_stop_boxed_3027_, v_b_3025_);
    lean_dec_ref(v_as_3022_);
    return v_res_3028_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__1;
    v___x_3033_ = l_Lean_MessageData_ofFormat(v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__3;
    v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
    return v___x_3036_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    v___x_3038_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__5;
    v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(
    mut v___x_3040_: *mut LeanObject,
    mut v_as_x27_3041_: *mut LeanObject,
    mut v_b_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
    mut v___y_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_reuseFailAlloc_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: usize = 0;
    let mut v___x_3109_: usize = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3041_) == 0 {
                    lean_dec_ref(v___x_3040_);
                    v___x_3046_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3046_, 0, v_b_3042_);
                    return v___x_3046_;
                } else {
                    v_head_3047_ = lean_ctor_get(v_as_x27_3041_, 0);
                    v_tail_3048_ = lean_ctor_get(v_as_x27_3041_, 1);
                    v___x_3049_ = l_Lean_NameSet_contains(v_b_3042_, v_head_3047_);
                    if v___x_3049_ == 0 {
                        lean_inc_n(v_head_3047_, 2);
                        v___x_3050_ = l_Lean_NameSet_insert(v_b_3042_, v_head_3047_);
                        lean_inc_ref(v___x_3040_);
                        v___x_3051_ =
                            l_Lean_Environment_find_x3f(v___x_3040_, v_head_3047_, v___x_3049_);
                        if lean_obj_tag(v___x_3051_) == 1 {
                            v_val_3052_ = lean_ctor_get(v___x_3051_, 0);
                            lean_inc(v_val_3052_);
                            lean_dec_ref_known(v___x_3051_, 1);
                            v___x_3053_ = l_Lean_ConstantInfo_type(v_val_3052_);
                            lean_dec(v_val_3052_);
                            lean_inc(v_head_3047_);
                            v___x_3054_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_univParamsGrouped(v___x_3053_, v_head_3047_);
                            v_size_3055_ = lean_ctor_get(v___x_3054_, 0);
                            v_buckets_3056_ = lean_ctor_get(v___x_3054_, 1);
                            v_isSharedCheck_3114_ = (!lean_is_exclusive(v___x_3054_)) as u8;
                            if v_isSharedCheck_3114_ == 0 {
                                v___x_3058_ = v___x_3054_;
                                v_isShared_3059_ = v_isSharedCheck_3114_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_buckets_3056_);
                                lean_inc(v_size_3055_);
                                lean_dec(v___x_3054_);
                                v___x_3058_ = lean_box(0);
                                v_isShared_3059_ = v_isSharedCheck_3114_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3051_);
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
                lean_dec(v_size_3055_);
                v___x_3104_ = lean_unsigned_to_nat(0);
                v___x_3105_ = lean_array_get_size(v_buckets_3056_);
                v___x_3106_ = lean_nat_dec_lt(v___x_3104_, v___x_3105_);
                if v___x_3106_ == 0 {
                    lean_dec_ref(v_buckets_3056_);
                    v___y_3062_ = v___x_3103_;
                    state = 2;
                    continue;
                } else {
                    v___x_3107_ = lean_nat_dec_le(v___x_3105_, v___x_3105_);
                    if v___x_3107_ == 0 {
                        if v___x_3106_ == 0 {
                            lean_dec_ref(v_buckets_3056_);
                            v___y_3062_ = v___x_3103_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3108_ = 0usize;
                            v___x_3109_ = lean_usize_of_nat(v___x_3105_);
                            v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_buckets_3056_, v___x_3108_, v___x_3109_, v___x_3103_);
                            lean_dec_ref(v_buckets_3056_);
                            v___y_3062_ = v___x_3110_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3111_ = 0usize;
                        v___x_3112_ = lean_usize_of_nat(v___x_3105_);
                        v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__5(v_buckets_3056_, v___x_3111_, v___x_3112_, v___x_3103_);
                        lean_dec_ref(v_buckets_3056_);
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
                v___x_3065_ = lean_unsigned_to_nat(0);
                v___x_3066_ = lean_nat_dec_eq(v___x_3064_, v___x_3065_);
                if v___x_3066_ == 0 {
                    v___x_3067_ = l_Lean_Elab_Command_getRef___redArg(v___y_3043_);
                    if lean_obj_tag(v___x_3067_) == 0 {
                        v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
                        lean_inc(v_a_3068_);
                        lean_dec_ref_known(v___x_3067_, 1);
                        v___x_3069_ = lean_array_to_list(v___x_3063_);
                        v___x_3070_ = lean_box(0);
                        v___x_3071_ = l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2(v___x_3069_, v___x_3070_);
                        v___x_3072_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__2);
                        v___x_3073_ = l_Lean_MessageData_joinSep(v___x_3071_, v___x_3072_);
                        v___x_3074_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__2___closed__1);
                        lean_inc(v_head_3047_);
                        v___x_3075_ = l_Lean_MessageData_ofConstName(v_head_3047_, v___x_3066_);
                        if v_isShared_3059_ == 0 {
                            lean_ctor_set_tag(v___x_3058_, 7);
                            lean_ctor_set(v___x_3058_, 1, v___x_3075_);
                            lean_ctor_set(v___x_3058_, 0, v___x_3074_);
                            v___x_3077_ = v___x_3058_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3093_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3074_);
                            lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3075_);
                            v___x_3077_ = v_reuseFailAlloc_3093_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3063_);
                        lean_del_object(v___x_3058_);
                        lean_dec(v___x_3050_);
                        lean_dec_ref(v___x_3040_);
                        v_a_3094_ = lean_ctor_get(v___x_3067_, 0);
                        v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3067_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3067_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3094_);
                            lean_dec(v___x_3067_);
                            v___x_3096_ = lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3063_);
                    lean_del_object(v___x_3058_);
                    v_as_x27_3041_ = v_tail_3048_;
                    v_b_3042_ = v___x_3050_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v___x_3078_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__4);
                v___x_3079_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3079_, 0, v___x_3077_);
                lean_ctor_set(v___x_3079_, 1, v___x_3078_);
                v___x_3080_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3080_, 0, v___x_3079_);
                lean_ctor_set(v___x_3080_, 1, v___x_3073_);
                v___x_3081_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg___closed__6);
                v___x_3082_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3082_, 0, v___x_3080_);
                lean_ctor_set(v___x_3082_, 1, v___x_3081_);
                v___x_3083_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3(v___x_3060_, v_a_3068_, v___x_3082_, v___y_3043_, v___y_3044_);
                lean_dec(v_a_3068_);
                if lean_obj_tag(v___x_3083_) == 0 {
                    lean_dec_ref_known(v___x_3083_, 1);
                    v_as_x27_3041_ = v_tail_3048_;
                    v_b_3042_ = v___x_3050_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_3050_);
                    lean_dec_ref(v___x_3040_);
                    v_a_3085_ = lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3092_ = (!lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3092_ == 0 {
                        v___x_3087_ = v___x_3083_;
                        v_isShared_3088_ = v_isSharedCheck_3092_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3085_);
                        lean_dec(v___x_3083_);
                        v___x_3087_ = lean_box(0);
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
                    v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
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
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
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
    mut v___x_3117_: *mut LeanObject,
    mut v_as_x27_3118_: *mut LeanObject,
    mut v_b_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3123_: *mut LeanObject = core::ptr::null_mut();
    v_res_3123_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(
            v___x_3117_,
            v_as_x27_3118_,
            v_b_3119_,
            v___y_3120_,
            v___y_3121_,
        );
    lean_dec(v___y_3121_);
    lean_dec_ref(v___y_3120_);
    lean_dec(v_as_x27_3118_);
    return v_res_3123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14(
    mut v___x_3124_: *mut LeanObject,
    mut v_as_3125_: *mut LeanObject,
    mut v_sz_3126_: usize,
    mut v_i_3127_: usize,
    mut v_b_3128_: *mut LeanObject,
    mut v___y_3129_: *mut LeanObject,
    mut v___y_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v_a_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: usize = 0;
    let mut v___x_3146_: usize = 0;
    let mut v_reuseFailAlloc_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v_unused_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3132_ = lean_usize_dec_lt(v_i_3127_, v_sz_3126_);
                if v___x_3132_ == 0 {
                    lean_dec_ref(v___x_3124_);
                    v___x_3133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3133_, 0, v_b_3128_);
                    return v___x_3133_;
                } else {
                    v_snd_3134_ = lean_ctor_get(v_b_3128_, 1);
                    v_isSharedCheck_3157_ = (!lean_is_exclusive(v_b_3128_)) as u8;
                    if v_isSharedCheck_3157_ == 0 {
                        v_unused_3158_ = lean_ctor_get(v_b_3128_, 0);
                        lean_dec(v_unused_3158_);
                        v___x_3136_ = v_b_3128_;
                        v_isShared_3137_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3134_);
                        lean_dec(v_b_3128_);
                        v___x_3136_ = lean_box(0);
                        v_isShared_3137_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3138_ = lean_array_uget_borrowed(v_as_3125_, v_i_3127_);
                lean_inc(v_a_3138_);
                v___x_3139_ = l_Lean_Linter_getNewDecls(v_a_3138_);
                lean_inc_ref(v___x_3124_);
                v___x_3140_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3124_, v___x_3139_, v_snd_3134_, v___y_3129_, v___y_3130_);
                lean_dec(v___x_3139_);
                if lean_obj_tag(v___x_3140_) == 0 {
                    v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
                    lean_inc(v_a_3141_);
                    lean_dec_ref_known(v___x_3140_, 1);
                    v___x_3142_ = lean_box(0);
                    if v_isShared_3137_ == 0 {
                        lean_ctor_set(v___x_3136_, 1, v_a_3141_);
                        lean_ctor_set(v___x_3136_, 0, v___x_3142_);
                        v___x_3144_ = v___x_3136_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3142_);
                        lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_a_3141_);
                        v___x_3144_ = v_reuseFailAlloc_3148_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3136_);
                    lean_dec_ref(v___x_3124_);
                    v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
                    v_isSharedCheck_3156_ = (!lean_is_exclusive(v___x_3140_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v___x_3151_ = v___x_3140_;
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3149_);
                        lean_dec(v___x_3140_);
                        v___x_3151_ = lean_box(0);
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
                    v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
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
    mut v___x_3159_: *mut LeanObject,
    mut v_as_3160_: *mut LeanObject,
    mut v_sz_3161_: *mut LeanObject,
    mut v_i_3162_: *mut LeanObject,
    mut v_b_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3167_: usize = 0;
    let mut v_i_boxed_3168_: usize = 0;
    let mut v_res_3169_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3167_ = lean_unbox_usize(v_sz_3161_);
    lean_dec(v_sz_3161_);
    v_i_boxed_3168_ = lean_unbox_usize(v_i_3162_);
    lean_dec(v_i_3162_);
    v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12_spec__14(v___x_3159_, v_as_3160_, v_sz_boxed_3167_, v_i_boxed_3168_, v_b_3163_, v___y_3164_, v___y_3165_);
    lean_dec(v___y_3165_);
    lean_dec_ref(v___y_3164_);
    lean_dec_ref(v_as_3160_);
    return v_res_3169_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(
    mut v___x_3170_: *mut LeanObject,
    mut v_as_3171_: *mut LeanObject,
    mut v_sz_3172_: usize,
    mut v_i_3173_: usize,
    mut v_b_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3183_: u8 = 0;
    let mut v_a_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_unused_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3178_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
                if v___x_3178_ == 0 {
                    lean_dec_ref(v___x_3170_);
                    v___x_3179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3179_, 0, v_b_3174_);
                    return v___x_3179_;
                } else {
                    v_snd_3180_ = lean_ctor_get(v_b_3174_, 1);
                    v_isSharedCheck_3203_ = (!lean_is_exclusive(v_b_3174_)) as u8;
                    if v_isSharedCheck_3203_ == 0 {
                        v_unused_3204_ = lean_ctor_get(v_b_3174_, 0);
                        lean_dec(v_unused_3204_);
                        v___x_3182_ = v_b_3174_;
                        v_isShared_3183_ = v_isSharedCheck_3203_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3180_);
                        lean_dec(v_b_3174_);
                        v___x_3182_ = lean_box(0);
                        v_isShared_3183_ = v_isSharedCheck_3203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3184_ = lean_array_uget_borrowed(v_as_3171_, v_i_3173_);
                lean_inc(v_a_3184_);
                v___x_3185_ = l_Lean_Linter_getNewDecls(v_a_3184_);
                lean_inc_ref(v___x_3170_);
                v___x_3186_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3170_, v___x_3185_, v_snd_3180_, v___y_3175_, v___y_3176_);
                lean_dec(v___x_3185_);
                if lean_obj_tag(v___x_3186_) == 0 {
                    v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
                    lean_inc(v_a_3187_);
                    lean_dec_ref_known(v___x_3186_, 1);
                    v___x_3188_ = lean_box(0);
                    if v_isShared_3183_ == 0 {
                        lean_ctor_set(v___x_3182_, 1, v_a_3187_);
                        lean_ctor_set(v___x_3182_, 0, v___x_3188_);
                        v___x_3190_ = v___x_3182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3188_);
                        lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_a_3187_);
                        v___x_3190_ = v_reuseFailAlloc_3194_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3182_);
                    lean_dec_ref(v___x_3170_);
                    v_a_3195_ = lean_ctor_get(v___x_3186_, 0);
                    v_isSharedCheck_3202_ = (!lean_is_exclusive(v___x_3186_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3197_ = v___x_3186_;
                        v_isShared_3198_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3195_);
                        lean_dec(v___x_3186_);
                        v___x_3197_ = lean_box(0);
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
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
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
    mut v___x_3205_: *mut LeanObject,
    mut v_as_3206_: *mut LeanObject,
    mut v_sz_3207_: *mut LeanObject,
    mut v_i_3208_: *mut LeanObject,
    mut v_b_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3213_: usize = 0;
    let mut v_i_boxed_3214_: usize = 0;
    let mut v_res_3215_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3213_ = lean_unbox_usize(v_sz_3207_);
    lean_dec(v_sz_3207_);
    v_i_boxed_3214_ = lean_unbox_usize(v_i_3208_);
    lean_dec(v_i_3208_);
    v_res_3215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(v___x_3205_, v_as_3206_, v_sz_boxed_3213_, v_i_boxed_3214_, v_b_3209_, v___y_3210_, v___y_3211_);
    lean_dec(v___y_3211_);
    lean_dec_ref(v___y_3210_);
    lean_dec_ref(v_as_3206_);
    return v_res_3215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(
    mut v_init_3216_: *mut LeanObject,
    mut v___x_3217_: *mut LeanObject,
    mut v_n_3218_: *mut LeanObject,
    mut v_b_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3226_: usize = 0;
    let mut v___x_3227_: usize = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v_fst_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v_a_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_vs_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3255_: usize = 0;
    let mut v___x_3256_: usize = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_fst_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_3218_) == 0 {
                    v_cs_3223_ = lean_ctor_get(v_n_3218_, 0);
                    v___x_3224_ = lean_box(0);
                    v___x_3225_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3225_, 0, v___x_3224_);
                    lean_ctor_set(v___x_3225_, 1, v_b_3219_);
                    v_sz_3226_ = lean_array_size(v_cs_3223_);
                    v___x_3227_ = 0usize;
                    v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11(v_init_3216_, v___x_3217_, v_cs_3223_, v_sz_3226_, v___x_3227_, v___x_3225_, v___y_3220_, v___y_3221_);
                    if lean_obj_tag(v___x_3228_) == 0 {
                        v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
                        v_isSharedCheck_3243_ = (!lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3243_ == 0 {
                            v___x_3231_ = v___x_3228_;
                            v_isShared_3232_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3229_);
                            lean_dec(v___x_3228_);
                            v___x_3231_ = lean_box(0);
                            v_isShared_3232_ = v_isSharedCheck_3243_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3244_ = lean_ctor_get(v___x_3228_, 0);
                        v_isSharedCheck_3251_ = (!lean_is_exclusive(v___x_3228_)) as u8;
                        if v_isSharedCheck_3251_ == 0 {
                            v___x_3246_ = v___x_3228_;
                            v_isShared_3247_ = v_isSharedCheck_3251_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3244_);
                            lean_dec(v___x_3228_);
                            v___x_3246_ = lean_box(0);
                            v_isShared_3247_ = v_isSharedCheck_3251_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3252_ = lean_ctor_get(v_n_3218_, 0);
                    v___x_3253_ = lean_box(0);
                    v___x_3254_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3254_, 0, v___x_3253_);
                    lean_ctor_set(v___x_3254_, 1, v_b_3219_);
                    v_sz_3255_ = lean_array_size(v_vs_3252_);
                    v___x_3256_ = 0usize;
                    v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__12(v___x_3217_, v_vs_3252_, v_sz_3255_, v___x_3256_, v___x_3254_, v___y_3220_, v___y_3221_);
                    if lean_obj_tag(v___x_3257_) == 0 {
                        v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                        v_isSharedCheck_3272_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3272_ == 0 {
                            v___x_3260_ = v___x_3257_;
                            v_isShared_3261_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3258_);
                            lean_dec(v___x_3257_);
                            v___x_3260_ = lean_box(0);
                            v_isShared_3261_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3273_ = lean_ctor_get(v___x_3257_, 0);
                        v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                        if v_isSharedCheck_3280_ == 0 {
                            v___x_3275_ = v___x_3257_;
                            v_isShared_3276_ = v_isSharedCheck_3280_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3273_);
                            lean_dec(v___x_3257_);
                            v___x_3275_ = lean_box(0);
                            v_isShared_3276_ = v_isSharedCheck_3280_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3233_ = lean_ctor_get(v_a_3229_, 0);
                if lean_obj_tag(v_fst_3233_) == 0 {
                    v_snd_3234_ = lean_ctor_get(v_a_3229_, 1);
                    lean_inc(v_snd_3234_);
                    lean_dec(v_a_3229_);
                    v___x_3235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3235_, 0, v_snd_3234_);
                    if v_isShared_3232_ == 0 {
                        lean_ctor_set(v___x_3231_, 0, v___x_3235_);
                        v___x_3237_ = v___x_3231_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                        v___x_3237_ = v_reuseFailAlloc_3238_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3233_);
                    lean_dec(v_a_3229_);
                    v_val_3239_ = lean_ctor_get(v_fst_3233_, 0);
                    lean_inc(v_val_3239_);
                    lean_dec_ref_known(v_fst_3233_, 1);
                    if v_isShared_3232_ == 0 {
                        lean_ctor_set(v___x_3231_, 0, v_val_3239_);
                        v___x_3241_ = v___x_3231_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_val_3239_);
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
                    v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
                    v___x_3249_ = v_reuseFailAlloc_3250_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3249_;
            }
            6 => {
                v_fst_3262_ = lean_ctor_get(v_a_3258_, 0);
                if lean_obj_tag(v_fst_3262_) == 0 {
                    v_snd_3263_ = lean_ctor_get(v_a_3258_, 1);
                    lean_inc(v_snd_3263_);
                    lean_dec(v_a_3258_);
                    v___x_3264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3264_, 0, v_snd_3263_);
                    if v_isShared_3261_ == 0 {
                        lean_ctor_set(v___x_3260_, 0, v___x_3264_);
                        v___x_3266_ = v___x_3260_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
                        v___x_3266_ = v_reuseFailAlloc_3267_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3262_);
                    lean_dec(v_a_3258_);
                    v_val_3268_ = lean_ctor_get(v_fst_3262_, 0);
                    lean_inc(v_val_3268_);
                    lean_dec_ref_known(v_fst_3262_, 1);
                    if v_isShared_3261_ == 0 {
                        lean_ctor_set(v___x_3260_, 0, v_val_3268_);
                        v___x_3270_ = v___x_3260_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_val_3268_);
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
                    v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
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
    mut v_init_3281_: *mut LeanObject,
    mut v___x_3282_: *mut LeanObject,
    mut v_as_3283_: *mut LeanObject,
    mut v_sz_3284_: usize,
    mut v_i_3285_: usize,
    mut v_b_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_a_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: usize = 0;
    let mut v___x_3314_: usize = 0;
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_a_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3290_ = lean_usize_dec_lt(v_i_3285_, v_sz_3284_);
                if v___x_3290_ == 0 {
                    lean_dec_ref(v___x_3282_);
                    v___x_3291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3291_, 0, v_b_3286_);
                    return v___x_3291_;
                } else {
                    v_snd_3292_ = lean_ctor_get(v_b_3286_, 1);
                    v_isSharedCheck_3326_ = (!lean_is_exclusive(v_b_3286_)) as u8;
                    if v_isSharedCheck_3326_ == 0 {
                        v_unused_3327_ = lean_ctor_get(v_b_3286_, 0);
                        lean_dec(v_unused_3327_);
                        v___x_3294_ = v_b_3286_;
                        v_isShared_3295_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3292_);
                        lean_dec(v_b_3286_);
                        v___x_3294_ = lean_box(0);
                        v_isShared_3295_ = v_isSharedCheck_3326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3296_ = lean_array_uget_borrowed(v_as_3283_, v_i_3285_);
                lean_inc(v_snd_3292_);
                lean_inc_ref(v___x_3282_);
                v___x_3297_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3281_, v___x_3282_, v_a_3296_, v_snd_3292_, v___y_3287_, v___y_3288_);
                if lean_obj_tag(v___x_3297_) == 0 {
                    v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3317_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3300_ = v___x_3297_;
                        v_isShared_3301_ = v_isSharedCheck_3317_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3298_);
                        lean_dec(v___x_3297_);
                        v___x_3300_ = lean_box(0);
                        v_isShared_3301_ = v_isSharedCheck_3317_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3294_);
                    lean_dec(v_snd_3292_);
                    lean_dec_ref(v___x_3282_);
                    v_a_3318_ = lean_ctor_get(v___x_3297_, 0);
                    v_isSharedCheck_3325_ = (!lean_is_exclusive(v___x_3297_)) as u8;
                    if v_isSharedCheck_3325_ == 0 {
                        v___x_3320_ = v___x_3297_;
                        v_isShared_3321_ = v_isSharedCheck_3325_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3318_);
                        lean_dec(v___x_3297_);
                        v___x_3320_ = lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3325_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3298_) == 0 {
                    lean_dec_ref(v___x_3282_);
                    v___x_3302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3302_, 0, v_a_3298_);
                    if v_isShared_3295_ == 0 {
                        lean_ctor_set(v___x_3294_, 0, v___x_3302_);
                        v___x_3304_ = v___x_3294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3302_);
                        lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_snd_3292_);
                        v___x_3304_ = v_reuseFailAlloc_3308_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3300_);
                    lean_dec(v_snd_3292_);
                    v_a_3309_ = lean_ctor_get(v_a_3298_, 0);
                    lean_inc(v_a_3309_);
                    lean_dec_ref_known(v_a_3298_, 1);
                    v___x_3310_ = lean_box(0);
                    if v_isShared_3295_ == 0 {
                        lean_ctor_set(v___x_3294_, 1, v_a_3309_);
                        lean_ctor_set(v___x_3294_, 0, v___x_3310_);
                        v___x_3312_ = v___x_3294_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3310_);
                        lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_a_3309_);
                        v___x_3312_ = v_reuseFailAlloc_3316_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3301_ == 0 {
                    lean_ctor_set(v___x_3300_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
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
                    v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
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
    mut v_init_3328_: *mut LeanObject,
    mut v___x_3329_: *mut LeanObject,
    mut v_as_3330_: *mut LeanObject,
    mut v_sz_3331_: *mut LeanObject,
    mut v_i_3332_: *mut LeanObject,
    mut v_b_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3337_: usize = 0;
    let mut v_i_boxed_3338_: usize = 0;
    let mut v_res_3339_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3337_ = lean_unbox_usize(v_sz_3331_);
    lean_dec(v_sz_3331_);
    v_i_boxed_3338_ = lean_unbox_usize(v_i_3332_);
    lean_dec(v_i_3332_);
    v_res_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9_spec__11(v_init_3328_, v___x_3329_, v_as_3330_, v_sz_boxed_3337_, v_i_boxed_3338_, v_b_3333_, v___y_3334_, v___y_3335_);
    lean_dec(v___y_3335_);
    lean_dec_ref(v___y_3334_);
    lean_dec_ref(v_as_3330_);
    lean_dec(v_init_3328_);
    return v_res_3339_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9___boxed(
    mut v_init_3340_: *mut LeanObject,
    mut v___x_3341_: *mut LeanObject,
    mut v_n_3342_: *mut LeanObject,
    mut v_b_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3347_: *mut LeanObject = core::ptr::null_mut();
    v_res_3347_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3340_, v___x_3341_, v_n_3342_, v_b_3343_, v___y_3344_, v___y_3345_);
    lean_dec(v___y_3345_);
    lean_dec_ref(v___y_3344_);
    lean_dec_ref(v_n_3342_);
    lean_dec(v_init_3340_);
    return v_res_3347_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14(
    mut v___x_3348_: *mut LeanObject,
    mut v_as_3349_: *mut LeanObject,
    mut v_sz_3350_: usize,
    mut v_i_3351_: usize,
    mut v_b_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v_a_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: usize = 0;
    let mut v___x_3370_: usize = 0;
    let mut v_reuseFailAlloc_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_unused_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3356_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
                if v___x_3356_ == 0 {
                    lean_dec_ref(v___x_3348_);
                    v___x_3357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3357_, 0, v_b_3352_);
                    return v___x_3357_;
                } else {
                    v_snd_3358_ = lean_ctor_get(v_b_3352_, 1);
                    v_isSharedCheck_3381_ = (!lean_is_exclusive(v_b_3352_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v_unused_3382_ = lean_ctor_get(v_b_3352_, 0);
                        lean_dec(v_unused_3382_);
                        v___x_3360_ = v_b_3352_;
                        v_isShared_3361_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3358_);
                        lean_dec(v_b_3352_);
                        v___x_3360_ = lean_box(0);
                        v_isShared_3361_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3362_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
                lean_inc(v_a_3362_);
                v___x_3363_ = l_Lean_Linter_getNewDecls(v_a_3362_);
                lean_inc_ref(v___x_3348_);
                v___x_3364_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3348_, v___x_3363_, v_snd_3358_, v___y_3353_, v___y_3354_);
                lean_dec(v___x_3363_);
                if lean_obj_tag(v___x_3364_) == 0 {
                    v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
                    lean_inc(v_a_3365_);
                    lean_dec_ref_known(v___x_3364_, 1);
                    v___x_3366_ = lean_box(0);
                    if v_isShared_3361_ == 0 {
                        lean_ctor_set(v___x_3360_, 1, v_a_3365_);
                        lean_ctor_set(v___x_3360_, 0, v___x_3366_);
                        v___x_3368_ = v___x_3360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3366_);
                        lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_a_3365_);
                        v___x_3368_ = v_reuseFailAlloc_3372_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3360_);
                    lean_dec_ref(v___x_3348_);
                    v_a_3373_ = lean_ctor_get(v___x_3364_, 0);
                    v_isSharedCheck_3380_ = (!lean_is_exclusive(v___x_3364_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v___x_3375_ = v___x_3364_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3373_);
                        lean_dec(v___x_3364_);
                        v___x_3375_ = lean_box(0);
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
                    v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
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
    mut v___x_3383_: *mut LeanObject,
    mut v_as_3384_: *mut LeanObject,
    mut v_sz_3385_: *mut LeanObject,
    mut v_i_3386_: *mut LeanObject,
    mut v_b_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3391_: usize = 0;
    let mut v_i_boxed_3392_: usize = 0;
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3391_ = lean_unbox_usize(v_sz_3385_);
    lean_dec(v_sz_3385_);
    v_i_boxed_3392_ = lean_unbox_usize(v_i_3386_);
    lean_dec(v_i_3386_);
    v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10_spec__14(v___x_3383_, v_as_3384_, v_sz_boxed_3391_, v_i_boxed_3392_, v_b_3387_, v___y_3388_, v___y_3389_);
    lean_dec(v___y_3389_);
    lean_dec_ref(v___y_3388_);
    lean_dec_ref(v_as_3384_);
    return v_res_3393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(
    mut v___x_3394_: *mut LeanObject,
    mut v_as_3395_: *mut LeanObject,
    mut v_sz_3396_: usize,
    mut v_i_3397_: usize,
    mut v_b_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v_a_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: usize = 0;
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3426_: u8 = 0;
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v_unused_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
                if v___x_3402_ == 0 {
                    lean_dec_ref(v___x_3394_);
                    v___x_3403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3403_, 0, v_b_3398_);
                    return v___x_3403_;
                } else {
                    v_snd_3404_ = lean_ctor_get(v_b_3398_, 1);
                    v_isSharedCheck_3427_ = (!lean_is_exclusive(v_b_3398_)) as u8;
                    if v_isSharedCheck_3427_ == 0 {
                        v_unused_3428_ = lean_ctor_get(v_b_3398_, 0);
                        lean_dec(v_unused_3428_);
                        v___x_3406_ = v_b_3398_;
                        v_isShared_3407_ = v_isSharedCheck_3427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3404_);
                        lean_dec(v_b_3398_);
                        v___x_3406_ = lean_box(0);
                        v_isShared_3407_ = v_isSharedCheck_3427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3408_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
                lean_inc(v_a_3408_);
                v___x_3409_ = l_Lean_Linter_getNewDecls(v_a_3408_);
                lean_inc_ref(v___x_3394_);
                v___x_3410_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6___redArg(v___x_3394_, v___x_3409_, v_snd_3404_, v___y_3399_, v___y_3400_);
                lean_dec(v___x_3409_);
                if lean_obj_tag(v___x_3410_) == 0 {
                    v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
                    lean_inc(v_a_3411_);
                    lean_dec_ref_known(v___x_3410_, 1);
                    v___x_3412_ = lean_box(0);
                    if v_isShared_3407_ == 0 {
                        lean_ctor_set(v___x_3406_, 1, v_a_3411_);
                        lean_ctor_set(v___x_3406_, 0, v___x_3412_);
                        v___x_3414_ = v___x_3406_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3412_);
                        lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_a_3411_);
                        v___x_3414_ = v_reuseFailAlloc_3418_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3406_);
                    lean_dec_ref(v___x_3394_);
                    v_a_3419_ = lean_ctor_get(v___x_3410_, 0);
                    v_isSharedCheck_3426_ = (!lean_is_exclusive(v___x_3410_)) as u8;
                    if v_isSharedCheck_3426_ == 0 {
                        v___x_3421_ = v___x_3410_;
                        v_isShared_3422_ = v_isSharedCheck_3426_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3419_);
                        lean_dec(v___x_3410_);
                        v___x_3421_ = lean_box(0);
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
                    v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
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
    mut v___x_3429_: *mut LeanObject,
    mut v_as_3430_: *mut LeanObject,
    mut v_sz_3431_: *mut LeanObject,
    mut v_i_3432_: *mut LeanObject,
    mut v_b_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3437_: usize = 0;
    let mut v_i_boxed_3438_: usize = 0;
    let mut v_res_3439_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3437_ = lean_unbox_usize(v_sz_3431_);
    lean_dec(v_sz_3431_);
    v_i_boxed_3438_ = lean_unbox_usize(v_i_3432_);
    lean_dec(v_i_3432_);
    v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(v___x_3429_, v_as_3430_, v_sz_boxed_3437_, v_i_boxed_3438_, v_b_3433_, v___y_3434_, v___y_3435_);
    lean_dec(v___y_3435_);
    lean_dec_ref(v___y_3434_);
    lean_dec_ref(v_as_3430_);
    return v_res_3439_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(
    mut v___x_3440_: *mut LeanObject,
    mut v_t_3441_: *mut LeanObject,
    mut v_init_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v_a_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3460_: usize = 0;
    let mut v___x_3461_: usize = 0;
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v_fst_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_a_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3446_ = lean_ctor_get(v_t_3441_, 0);
                v_tail_3447_ = lean_ctor_get(v_t_3441_, 1);
                lean_inc_ref(v___x_3440_);
                lean_inc(v_init_3442_);
                v___x_3448_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__9(v_init_3442_, v___x_3440_, v_root_3446_, v_init_3442_, v___y_3443_, v___y_3444_);
                lean_dec(v_init_3442_);
                if lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3485_ = (!lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3451_ = v___x_3448_;
                        v_isShared_3452_ = v_isSharedCheck_3485_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3449_);
                        lean_dec(v___x_3448_);
                        v___x_3451_ = lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3485_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3440_);
                    v_a_3486_ = lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3493_ = (!lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3493_ == 0 {
                        v___x_3488_ = v___x_3448_;
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3486_);
                        lean_dec(v___x_3448_);
                        v___x_3488_ = lean_box(0);
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3449_) == 0 {
                    lean_dec_ref(v___x_3440_);
                    v_a_3453_ = lean_ctor_get(v_a_3449_, 0);
                    lean_inc(v_a_3453_);
                    lean_dec_ref_known(v_a_3449_, 1);
                    if v_isShared_3452_ == 0 {
                        lean_ctor_set(v___x_3451_, 0, v_a_3453_);
                        v___x_3455_ = v___x_3451_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3453_);
                        v___x_3455_ = v_reuseFailAlloc_3456_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3451_);
                    v_a_3457_ = lean_ctor_get(v_a_3449_, 0);
                    lean_inc(v_a_3457_);
                    lean_dec_ref_known(v_a_3449_, 1);
                    v___x_3458_ = lean_box(0);
                    v___x_3459_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3459_, 0, v___x_3458_);
                    lean_ctor_set(v___x_3459_, 1, v_a_3457_);
                    v_sz_3460_ = lean_array_size(v_tail_3447_);
                    v___x_3461_ = 0usize;
                    v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7_spec__10(v___x_3440_, v_tail_3447_, v_sz_3460_, v___x_3461_, v___x_3459_, v___y_3443_, v___y_3444_);
                    if lean_obj_tag(v___x_3462_) == 0 {
                        v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
                        v_isSharedCheck_3476_ = (!lean_is_exclusive(v___x_3462_)) as u8;
                        if v_isSharedCheck_3476_ == 0 {
                            v___x_3465_ = v___x_3462_;
                            v_isShared_3466_ = v_isSharedCheck_3476_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3463_);
                            lean_dec(v___x_3462_);
                            v___x_3465_ = lean_box(0);
                            v_isShared_3466_ = v_isSharedCheck_3476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3477_ = lean_ctor_get(v___x_3462_, 0);
                        v_isSharedCheck_3484_ = (!lean_is_exclusive(v___x_3462_)) as u8;
                        if v_isSharedCheck_3484_ == 0 {
                            v___x_3479_ = v___x_3462_;
                            v_isShared_3480_ = v_isSharedCheck_3484_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3477_);
                            lean_dec(v___x_3462_);
                            v___x_3479_ = lean_box(0);
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
                v_fst_3467_ = lean_ctor_get(v_a_3463_, 0);
                if lean_obj_tag(v_fst_3467_) == 0 {
                    v_snd_3468_ = lean_ctor_get(v_a_3463_, 1);
                    lean_inc(v_snd_3468_);
                    lean_dec(v_a_3463_);
                    if v_isShared_3466_ == 0 {
                        lean_ctor_set(v___x_3465_, 0, v_snd_3468_);
                        v___x_3470_ = v___x_3465_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_snd_3468_);
                        v___x_3470_ = v_reuseFailAlloc_3471_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3467_);
                    lean_dec(v_a_3463_);
                    v_val_3472_ = lean_ctor_get(v_fst_3467_, 0);
                    lean_inc(v_val_3472_);
                    lean_dec_ref_known(v_fst_3467_, 1);
                    if v_isShared_3466_ == 0 {
                        lean_ctor_set(v___x_3465_, 0, v_val_3472_);
                        v___x_3474_ = v___x_3465_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_val_3472_);
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
                    v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
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
                    v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
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
    mut v___x_3494_: *mut LeanObject,
    mut v_t_3495_: *mut LeanObject,
    mut v_init_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_res_3500_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(
            v___x_3494_,
            v_t_3495_,
            v_init_3496_,
            v___y_3497_,
            v___y_3498_,
        );
    lean_dec(v___y_3498_);
    lean_dec_ref(v___y_3497_);
    lean_dec_ref(v_t_3495_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0(
    mut v_x_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut v_unused_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0(v___y_3502_, v___y_3503_);
                v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
                v_isSharedCheck_3546_ = (!lean_is_exclusive(v___x_3505_)) as u8;
                if v_isSharedCheck_3546_ == 0 {
                    v___x_3508_ = v___x_3505_;
                    v_isShared_3509_ = v_isSharedCheck_3546_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3506_);
                    lean_dec(v___x_3505_);
                    v___x_3508_ = lean_box(0);
                    v_isShared_3509_ = v_isSharedCheck_3546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3510_ = l_Lean_Linter_linter_checkUnivs;
                v___x_3511_ = l_Lean_Linter_getLinterValue(v___x_3510_, v_a_3506_);
                lean_dec(v_a_3506_);
                if v___x_3511_ == 0 {
                    v___x_3512_ = lean_box(0);
                    if v_isShared_3509_ == 0 {
                        lean_ctor_set(v___x_3508_, 0, v___x_3512_);
                        v___x_3514_ = v___x_3508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
                        v___x_3514_ = v_reuseFailAlloc_3515_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3516_ = lean_st_ref_get(v___y_3503_);
                    v_messages_3517_ = lean_ctor_get(v___x_3516_, 1);
                    lean_inc_ref(v_messages_3517_);
                    lean_dec(v___x_3516_);
                    v___x_3518_ = l_Lean_MessageLog_hasErrors(v_messages_3517_);
                    lean_dec_ref(v_messages_3517_);
                    if v___x_3518_ == 0 {
                        lean_del_object(v___x_3508_);
                        v___x_3519_ = lean_st_ref_get(v___y_3503_);
                        v___x_3520_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__1___redArg(v___y_3503_);
                        v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
                        lean_inc(v_a_3521_);
                        lean_dec_ref(v___x_3520_);
                        v_env_3522_ = lean_ctor_get(v___x_3519_, 0);
                        lean_inc_ref(v_env_3522_);
                        lean_dec(v___x_3519_);
                        v___x_3523_ = l_Lean_NameSet_empty;
                        v___x_3524_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__7(v_env_3522_, v_a_3521_, v___x_3523_, v___y_3502_, v___y_3503_);
                        lean_dec(v_a_3521_);
                        if lean_obj_tag(v___x_3524_) == 0 {
                            v_isSharedCheck_3532_ = (!lean_is_exclusive(v___x_3524_)) as u8;
                            if v_isSharedCheck_3532_ == 0 {
                                v_unused_3533_ = lean_ctor_get(v___x_3524_, 0);
                                lean_dec(v_unused_3533_);
                                v___x_3526_ = v___x_3524_;
                                v_isShared_3527_ = v_isSharedCheck_3532_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3524_);
                                v___x_3526_ = lean_box(0);
                                v_isShared_3527_ = v_isSharedCheck_3532_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3534_ = lean_ctor_get(v___x_3524_, 0);
                            v_isSharedCheck_3541_ = (!lean_is_exclusive(v___x_3524_)) as u8;
                            if v_isSharedCheck_3541_ == 0 {
                                v___x_3536_ = v___x_3524_;
                                v_isShared_3537_ = v_isSharedCheck_3541_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3534_);
                                lean_dec(v___x_3524_);
                                v___x_3536_ = lean_box(0);
                                v_isShared_3537_ = v_isSharedCheck_3541_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_3542_ = lean_box(0);
                        if v_isShared_3509_ == 0 {
                            lean_ctor_set(v___x_3508_, 0, v___x_3542_);
                            v___x_3544_ = v___x_3508_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
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
                v___x_3528_ = lean_box(0);
                if v_isShared_3527_ == 0 {
                    lean_ctor_set(v___x_3526_, 0, v___x_3528_);
                    v___x_3530_ = v___x_3526_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
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
                    v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
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
    mut v_x_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3551_: *mut LeanObject = core::ptr::null_mut();
    v_res_3551_ =
        l_Lean_Linter_CheckUnivs_checkUnivsLinter___lam__0(v_x_3547_, v___y_3548_, v___y_3549_);
    lean_dec(v___y_3549_);
    lean_dec_ref(v___y_3548_);
    lean_dec(v_x_3547_);
    return v_res_3551_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0(
    mut v_o_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    v___x_3570_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___redArg(v_o_3566_, v___y_3568_);
    return v___x_3570_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0___boxed(
    mut v_o_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3575_: *mut LeanObject = core::ptr::null_mut();
    v_res_3575_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__0_spec__0(v_o_3571_, v___y_3572_, v___y_3573_);
    lean_dec(v___y_3573_);
    lean_dec_ref(v___y_3572_);
    return v_res_3575_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6(
    mut v___x_3576_: *mut LeanObject,
    mut v_as_3577_: *mut LeanObject,
    mut v_as_x27_3578_: *mut LeanObject,
    mut v_b_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_3585_: *mut LeanObject,
    mut v_as_3586_: *mut LeanObject,
    mut v_as_x27_3587_: *mut LeanObject,
    mut v_b_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
    mut v___y_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_List_forIn_x27_loop___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__6(
        v___x_3585_,
        v_as_3586_,
        v_as_x27_3587_,
        v_b_3588_,
        v_a_3589_,
        v___y_3590_,
        v___y_3591_,
    );
    lean_dec(v___y_3591_);
    lean_dec_ref(v___y_3590_);
    lean_dec(v_as_x27_3587_);
    lean_dec(v_as_3586_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13(
    mut v_msgData_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___redArg(v_msgData_3594_, v___y_3596_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13___boxed(
    mut v_msgData_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3603_: *mut LeanObject = core::ptr::null_mut();
    v_res_3603_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_CheckUnivs_checkUnivsLinter_spec__3_spec__4_spec__5_spec__10_spec__13(v_msgData_3599_, v___y_3600_, v___y_3601_);
    lean_dec(v___y_3601_);
    lean_dec_ref(v___y_3600_);
    return v_res_3603_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_Linter_CheckUnivs_checkUnivsLinter;
    v___x_3606_ = l_Lean_Elab_Command_addLinter(v___x_3605_);
    return v___x_3606_;
}
pub unsafe fn l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2____boxed(
    mut v_a_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3608_: *mut LeanObject = core::ptr::null_mut();
    v_res_3608_ = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_();
    return v_res_3608_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_CheckUnivs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_initFn_00___x40_Lean_Linter_CheckUnivs_3900621596____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_checkUnivs = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_checkUnivs);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_CheckUnivs_0__Lean_Linter_CheckUnivs_initFn_00___x40_Lean_Linter_CheckUnivs_3475882223____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_CheckUnivs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_CheckUnivs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_CheckUnivs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_CheckUnivs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_CheckUnivs(builtin);
}
