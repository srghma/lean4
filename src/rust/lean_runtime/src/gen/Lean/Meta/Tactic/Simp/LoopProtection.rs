// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.LoopProtection
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Linter.Init
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_appArg_x21, l_Lean_Expr_hasFVar, l_Lean_mkFVar};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag,
    l_Lean_Linter_linterSetsExt, runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_Origin_key, l_Lean_Meta_SimpTheorem_getValue,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, l_Lean_Meta_Simp_SimpM_run___redArg,
    l_Lean_Meta_Simp_UsedSimps_toArray, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_dec_eq, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Meta::Tactic::Simp::Types::lean_simp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [108, 111, 111, 112, 105, 110, 103, 83, 105, 109, 112, 65, 114, 103, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,4734170744153359743 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<451> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 451, m_capacity: 451, m_length: 450, m_data: [87, 104, 101, 110, 32, 101, 110, 97, 98, 108, 101, 100, 44, 32, 96, 115, 105, 109, 112, 96, 32, 119, 105, 108, 108, 32, 99, 104, 101, 99, 107, 32, 105, 102, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 112, 97, 115, 115, 101, 100, 32, 97, 115, 32, 115, 105, 109, 112, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 40, 96, 115, 105, 109, 112, 32, 91, 116, 104, 109, 49, 93, 96, 41, 32, 97, 114, 101, 32, 112, 111, 115, 115, 105, 98, 108, 121, 32, 108, 111, 111, 112, 105, 110, 103, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 115, 105, 109, 112, 32, 115, 101, 116, 46, 10, 10, 77, 111, 114, 101, 32, 112, 114, 101, 99, 105, 115, 101, 108, 121, 44, 32, 105, 116, 32, 116, 114, 105, 101, 115, 32, 116, 111, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 104, 101, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 110, 100, 32, 99, 111, 109, 112, 108, 97, 105, 110, 115, 32, 105, 102, 32, 116, 104, 97, 116, 32, 102, 97, 105, 108, 115, 44, 32, 119, 104, 105, 99, 104, 32, 105, 116, 32, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 100, 111, 101, 115, 32, 98, 101, 99, 97, 117, 115, 101, 32, 111, 102, 32, 114, 117, 110, 110, 105, 110, 103, 32, 111, 117, 116, 32, 111, 102, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 114, 101, 108, 97, 116, 105, 118, 101, 108, 121, 32, 101, 120, 112, 101, 110, 115, 105, 118, 101, 32, 99, 104, 101, 99, 107, 44, 32, 115, 111, 32, 105, 116, 32, 105, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 98, 121, 32, 100, 101, 102, 97, 117, 108, 116, 44, 32, 97, 110, 100, 32, 111, 110, 108, 121, 32, 114, 117, 110, 32, 97, 102, 116, 101, 114, 32, 97, 32, 96, 115, 105, 109, 112, 96, 32, 99, 97, 108, 108, 32, 97, 99, 116, 117, 97, 108, 108, 121, 32, 102, 97, 105, 108, 101, 100, 32, 119, 105, 116, 104, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 101, 114, 114, 111, 114, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,492087047182689846 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,12613445789975699915 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,10068729174000177050 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 147, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 4, m_data: [226, 134, 147, 32, 226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 134, 144, 32, 0]};
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value: LeanStringObject<95> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 95,
        m_capacity: 95,
        m_length: 94,
        m_data: [
            89, 111, 117, 32, 99, 97, 110, 32, 100, 105, 115, 97, 98, 108, 101, 32, 97, 32, 115,
            105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 114, 111, 109, 32, 116,
            104, 101, 32, 100, 101, 102, 97, 117, 108, 116, 32, 115, 105, 109, 112, 32, 115, 101,
            116, 32, 98, 121, 32, 112, 97, 115, 115, 105, 110, 103, 32, 96, 45, 32, 116, 104, 101,
            111, 114, 101, 109, 78, 97, 109, 101, 96, 32, 116, 111, 32, 96, 115, 105, 109, 112, 96,
            46, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            80, 111, 115, 115, 105, 98, 108, 121, 32, 108, 111, 111, 112, 105, 110, 103, 32, 115,
            105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 58, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            80, 111, 115, 115, 105, 98, 108, 121, 32, 99, 97, 117, 115, 101, 100, 32, 98, 121, 58,
            32, 0,
        ],
    };
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100,
        105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111,
        112, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [32, 102, 97, 108, 115, 101, 96, 0],
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            108, 111, 111, 112, 80, 114, 111, 116, 101, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__0_value)
                as *mut LeanObject,
            3981491789317542566 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__1_value)
                as *mut LeanObject,
            11537002108020701424 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            108, 111, 111, 112, 32, 112, 114, 111, 116, 101, 99, 116, 105, 111, 110, 32, 102, 111,
            114, 32, 0,
        ],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            58, 32, 103, 111, 116, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_checkLoops___lam__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_checkLoops___lam__1___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(
    mut v_name_1441_: *mut LeanObject,
    mut v_decl_1442_: *mut LeanObject,
    mut v_ref_1443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut v_unused_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1445_ = lean_ctor_get(v_decl_1442_, 0);
                v_descr_1446_ = lean_ctor_get(v_decl_1442_, 1);
                v_deprecation_x3f_1447_ = lean_ctor_get(v_decl_1442_, 2);
                v___x_1448_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1449_ = (lean_unbox(v_defValue_1445_) as u8);
                lean_ctor_set_uint8(v___x_1448_, 0 as u32, v___x_1449_);
                lean_inc(v_deprecation_x3f_1447_);
                lean_inc_ref(v_descr_1446_);
                lean_inc_n(v_name_1441_, 2);
                v___x_1450_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1450_, 0, v_name_1441_);
                lean_ctor_set(v___x_1450_, 1, v_ref_1443_);
                lean_ctor_set(v___x_1450_, 2, v___x_1448_);
                lean_ctor_set(v___x_1450_, 3, v_descr_1446_);
                lean_ctor_set(v___x_1450_, 4, v_deprecation_x3f_1447_);
                v___x_1451_ = lean_register_option(v_name_1441_, v___x_1450_);
                if lean_obj_tag(v___x_1451_) == 0 {
                    v_isSharedCheck_1459_ = (!lean_is_exclusive(v___x_1451_)) as u8;
                    if v_isSharedCheck_1459_ == 0 {
                        v_unused_1460_ = lean_ctor_get(v___x_1451_, 0);
                        lean_dec(v_unused_1460_);
                        v___x_1453_ = v___x_1451_;
                        v_isShared_1454_ = v_isSharedCheck_1459_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1451_);
                        v___x_1453_ = lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1459_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1441_);
                    v_a_1461_ = lean_ctor_get(v___x_1451_, 0);
                    v_isSharedCheck_1468_ = (!lean_is_exclusive(v___x_1451_)) as u8;
                    if v_isSharedCheck_1468_ == 0 {
                        v___x_1463_ = v___x_1451_;
                        v_isShared_1464_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1461_);
                        lean_dec(v___x_1451_);
                        v___x_1463_ = lean_box(0);
                        v_isShared_1464_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1445_);
                v___x_1455_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1455_, 0, v_name_1441_);
                lean_ctor_set(v___x_1455_, 1, v_defValue_1445_);
                if v_isShared_1454_ == 0 {
                    lean_ctor_set(v___x_1453_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
                    v___x_1457_ = v_reuseFailAlloc_1458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1457_;
            }
            3 => {
                if v_isShared_1464_ == 0 {
                    v___x_1466_ = v___x_1463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1469_: *mut LeanObject,
    mut v_decl_1470_: *mut LeanObject,
    mut v_ref_1471_: *mut LeanObject,
    mut v_a_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1473_: *mut LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v_name_1469_, v_decl_1470_, v_ref_1471_);
    lean_dec_ref(v_decl_1470_);
    return v_res_1473_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1496_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1497_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_;
    v___x_1498_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4__spec__0(v___x_1495_, v___x_1496_, v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4____boxed(
    mut v_a_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1500_: *mut LeanObject = core::ptr::null_mut();
    v_res_1500_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
    return v_res_1500_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
    mut v_a_1501_: *mut LeanObject,
    mut v_usedTheorems_1502_: *mut LeanObject,
    mut v_a_x3f_1503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_unused_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_st_ref_take(v_a_1501_);
                v_cache_1506_ = lean_ctor_get(v___x_1505_, 0);
                v_congrCache_1507_ = lean_ctor_get(v___x_1505_, 1);
                v_dsimpCache_1508_ = lean_ctor_get(v___x_1505_, 2);
                v_numSteps_1509_ = lean_ctor_get(v___x_1505_, 4);
                v_diag_1510_ = lean_ctor_get(v___x_1505_, 5);
                v_isSharedCheck_1520_ = (!lean_is_exclusive(v___x_1505_)) as u8;
                if v_isSharedCheck_1520_ == 0 {
                    v_unused_1521_ = lean_ctor_get(v___x_1505_, 3);
                    lean_dec(v_unused_1521_);
                    v___x_1512_ = v___x_1505_;
                    v_isShared_1513_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1510_);
                    lean_inc(v_numSteps_1509_);
                    lean_inc(v_dsimpCache_1508_);
                    lean_inc(v_congrCache_1507_);
                    lean_inc(v_cache_1506_);
                    lean_dec(v___x_1505_);
                    v___x_1512_ = lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1520_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1513_ == 0 {
                    lean_ctor_set(v___x_1512_, 3, v_usedTheorems_1502_);
                    v___x_1515_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_cache_1506_);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_congrCache_1507_);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_dsimpCache_1508_);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_usedTheorems_1502_);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_numSteps_1509_);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_diag_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1516_ = lean_st_ref_set(v_a_1501_, v___x_1515_);
                v___x_1517_ = lean_box(0);
                v___x_1518_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1518_, 0, v___x_1517_);
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0___boxed(
    mut v_a_1522_: *mut LeanObject,
    mut v_usedTheorems_1523_: *mut LeanObject,
    mut v_a_x3f_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1526_: *mut LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
        v_a_1522_,
        v_usedTheorems_1523_,
        v_a_x3f_1524_,
    );
    lean_dec(v_a_x3f_1524_);
    lean_dec(v_a_1522_);
    return v_res_1526_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0() -> *mut LeanObject
{
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1527_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1() -> *mut LeanObject
{
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0_once),
        _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__0,
    );
    v___x_1529_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1529_, 0, v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2() -> *mut LeanObject
{
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = lean_unsigned_to_nat(0);
    v___x_1531_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1_once),
        _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__1,
    );
    v___x_1532_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1532_, 0, v___x_1531_);
    lean_ctor_set(v___x_1532_, 1, v___x_1530_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(
    mut v_x_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
    mut v_a_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_unused_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut v_a_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut v_unused_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1542_ = lean_st_ref_get(v_a_1536_);
                v___x_1543_ = lean_st_ref_take(v_a_1536_);
                v_cache_1544_ = lean_ctor_get(v___x_1543_, 0);
                v_congrCache_1545_ = lean_ctor_get(v___x_1543_, 1);
                v_dsimpCache_1546_ = lean_ctor_get(v___x_1543_, 2);
                v_numSteps_1547_ = lean_ctor_get(v___x_1543_, 4);
                v_diag_1548_ = lean_ctor_get(v___x_1543_, 5);
                v_isSharedCheck_1587_ = (!lean_is_exclusive(v___x_1543_)) as u8;
                if v_isSharedCheck_1587_ == 0 {
                    v_unused_1588_ = lean_ctor_get(v___x_1543_, 3);
                    lean_dec(v_unused_1588_);
                    v___x_1550_ = v___x_1543_;
                    v_isShared_1551_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1548_);
                    lean_inc(v_numSteps_1547_);
                    lean_inc(v_dsimpCache_1546_);
                    lean_inc(v_congrCache_1545_);
                    lean_inc(v_cache_1544_);
                    lean_dec(v___x_1543_);
                    v___x_1550_ = lean_box(0);
                    v_isShared_1551_ = v_isSharedCheck_1587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1552_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2,
                );
                if v_isShared_1551_ == 0 {
                    lean_ctor_set(v___x_1550_, 3, v___x_1552_);
                    v___x_1554_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_cache_1544_);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_congrCache_1545_);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_dsimpCache_1546_);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 3, v___x_1552_);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_numSteps_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_diag_1548_);
                    v___x_1554_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1555_ = lean_st_ref_set(v_a_1536_, v___x_1554_);
                v_usedTheorems_1556_ = lean_ctor_get(v___x_1542_, 3);
                lean_inc_ref(v_usedTheorems_1556_);
                lean_dec(v___x_1542_);
                lean_inc(v_a_1540_);
                lean_inc_ref(v_a_1539_);
                lean_inc(v_a_1538_);
                lean_inc_ref(v_a_1537_);
                lean_inc(v_a_1536_);
                lean_inc_ref(v_a_1535_);
                lean_inc(v_a_1534_);
                v_r_1557_ = lean_apply_8(
                    v_x_1533_,
                    v_a_1534_,
                    v_a_1535_,
                    v_a_1536_,
                    v_a_1537_,
                    v_a_1538_,
                    v_a_1539_,
                    v_a_1540_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_1557_) == 0 {
                    v_a_1558_ = lean_ctor_get(v_r_1557_, 0);
                    v_isSharedCheck_1574_ = (!lean_is_exclusive(v_r_1557_)) as u8;
                    if v_isSharedCheck_1574_ == 0 {
                        v___x_1560_ = v_r_1557_;
                        v_isShared_1561_ = v_isSharedCheck_1574_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1558_);
                        lean_dec(v_r_1557_);
                        v___x_1560_ = lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1574_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1575_ = lean_ctor_get(v_r_1557_, 0);
                    lean_inc(v_a_1575_);
                    lean_dec_ref_known(v_r_1557_, 1);
                    v___x_1576_ = lean_box(0);
                    v___x_1577_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                        v_a_1536_,
                        v_usedTheorems_1556_,
                        v___x_1576_,
                    );
                    v_isSharedCheck_1584_ = (!lean_is_exclusive(v___x_1577_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v_unused_1585_ = lean_ctor_get(v___x_1577_, 0);
                        lean_dec(v_unused_1585_);
                        v___x_1579_ = v___x_1577_;
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_1577_);
                        v___x_1579_ = lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_1558_);
                if v_isShared_1561_ == 0 {
                    lean_ctor_set_tag(v___x_1560_, 1);
                    v___x_1563_ = v___x_1560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1564_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                    v_a_1536_,
                    v_usedTheorems_1556_,
                    v___x_1563_,
                );
                lean_dec_ref(v___x_1563_);
                v_isSharedCheck_1571_ = (!lean_is_exclusive(v___x_1564_)) as u8;
                if v_isSharedCheck_1571_ == 0 {
                    v_unused_1572_ = lean_ctor_get(v___x_1564_, 0);
                    lean_dec(v_unused_1572_);
                    v___x_1566_ = v___x_1564_;
                    v_isShared_1567_ = v_isSharedCheck_1571_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_1564_);
                    v___x_1566_ = lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1567_ == 0 {
                    lean_ctor_set(v___x_1566_, 0, v_a_1558_);
                    v___x_1569_ = v___x_1566_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1558_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1569_;
            }
            7 => {
                if v_isShared_1580_ == 0 {
                    lean_ctor_set_tag(v___x_1579_, 1);
                    lean_ctor_set(v___x_1579_, 0, v_a_1575_);
                    v___x_1582_ = v___x_1579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1575_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___boxed(
    mut v_x_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
    mut v_a_1593_: *mut LeanObject,
    mut v_a_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg(
        v_x_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_,
    );
    lean_dec(v_a_1596_);
    lean_dec_ref(v_a_1595_);
    lean_dec(v_a_1594_);
    lean_dec_ref(v_a_1593_);
    lean_dec(v_a_1592_);
    lean_dec_ref(v_a_1591_);
    lean_dec(v_a_1590_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems(
    mut v_00_u03b1_1599_: *mut LeanObject,
    mut v_x_1600_: *mut LeanObject,
    mut v_a_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrCache_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dsimpCache_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_unused_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_a_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_unused_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v_unused_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = lean_st_ref_get(v_a_1603_);
                v___x_1610_ = lean_st_ref_take(v_a_1603_);
                v_cache_1611_ = lean_ctor_get(v___x_1610_, 0);
                v_congrCache_1612_ = lean_ctor_get(v___x_1610_, 1);
                v_dsimpCache_1613_ = lean_ctor_get(v___x_1610_, 2);
                v_numSteps_1614_ = lean_ctor_get(v___x_1610_, 4);
                v_diag_1615_ = lean_ctor_get(v___x_1610_, 5);
                v_isSharedCheck_1654_ = (!lean_is_exclusive(v___x_1610_)) as u8;
                if v_isSharedCheck_1654_ == 0 {
                    v_unused_1655_ = lean_ctor_get(v___x_1610_, 3);
                    lean_dec(v_unused_1655_);
                    v___x_1617_ = v___x_1610_;
                    v_isShared_1618_ = v_isSharedCheck_1654_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1615_);
                    lean_inc(v_numSteps_1614_);
                    lean_inc(v_dsimpCache_1613_);
                    lean_inc(v_congrCache_1612_);
                    lean_inc(v_cache_1611_);
                    lean_dec(v___x_1610_);
                    v___x_1617_ = lean_box(0);
                    v_isShared_1618_ = v_isSharedCheck_1654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1619_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___closed__2,
                );
                if v_isShared_1618_ == 0 {
                    lean_ctor_set(v___x_1617_, 3, v___x_1619_);
                    v___x_1621_ = v___x_1617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_cache_1611_);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_congrCache_1612_);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_dsimpCache_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___x_1619_);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_numSteps_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1653_, 5, v_diag_1615_);
                    v___x_1621_ = v_reuseFailAlloc_1653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1622_ = lean_st_ref_set(v_a_1603_, v___x_1621_);
                v_usedTheorems_1623_ = lean_ctor_get(v___x_1609_, 3);
                lean_inc_ref(v_usedTheorems_1623_);
                lean_dec(v___x_1609_);
                lean_inc(v_a_1607_);
                lean_inc_ref(v_a_1606_);
                lean_inc(v_a_1605_);
                lean_inc_ref(v_a_1604_);
                lean_inc(v_a_1603_);
                lean_inc_ref(v_a_1602_);
                lean_inc(v_a_1601_);
                v_r_1624_ = lean_apply_8(
                    v_x_1600_,
                    v_a_1601_,
                    v_a_1602_,
                    v_a_1603_,
                    v_a_1604_,
                    v_a_1605_,
                    v_a_1606_,
                    v_a_1607_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_1624_) == 0 {
                    v_a_1625_ = lean_ctor_get(v_r_1624_, 0);
                    v_isSharedCheck_1641_ = (!lean_is_exclusive(v_r_1624_)) as u8;
                    if v_isSharedCheck_1641_ == 0 {
                        v___x_1627_ = v_r_1624_;
                        v_isShared_1628_ = v_isSharedCheck_1641_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1625_);
                        lean_dec(v_r_1624_);
                        v___x_1627_ = lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1641_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1642_ = lean_ctor_get(v_r_1624_, 0);
                    lean_inc(v_a_1642_);
                    lean_dec_ref_known(v_r_1624_, 1);
                    v___x_1643_ = lean_box(0);
                    v___x_1644_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                        v_a_1603_,
                        v_usedTheorems_1623_,
                        v___x_1643_,
                    );
                    v_isSharedCheck_1651_ = (!lean_is_exclusive(v___x_1644_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v_unused_1652_ = lean_ctor_get(v___x_1644_, 0);
                        lean_dec(v_unused_1652_);
                        v___x_1646_ = v___x_1644_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_1644_);
                        v___x_1646_ = lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_1625_);
                if v_isShared_1628_ == 0 {
                    lean_ctor_set_tag(v___x_1627_, 1);
                    v___x_1630_ = v___x_1627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1625_);
                    v___x_1630_ = v_reuseFailAlloc_1640_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1631_ = l_Lean_Meta_Simp_withFreshUsedTheorems___redArg___lam__0(
                    v_a_1603_,
                    v_usedTheorems_1623_,
                    v___x_1630_,
                );
                lean_dec_ref(v___x_1630_);
                v_isSharedCheck_1638_ = (!lean_is_exclusive(v___x_1631_)) as u8;
                if v_isSharedCheck_1638_ == 0 {
                    v_unused_1639_ = lean_ctor_get(v___x_1631_, 0);
                    lean_dec(v_unused_1639_);
                    v___x_1633_ = v___x_1631_;
                    v_isShared_1634_ = v_isSharedCheck_1638_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_1631_);
                    v___x_1633_ = lean_box(0);
                    v_isShared_1634_ = v_isSharedCheck_1638_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1634_ == 0 {
                    lean_ctor_set(v___x_1633_, 0, v_a_1625_);
                    v___x_1636_ = v___x_1633_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1625_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1636_;
            }
            7 => {
                if v_isShared_1647_ == 0 {
                    lean_ctor_set_tag(v___x_1646_, 1);
                    lean_ctor_set(v___x_1646_, 0, v_a_1642_);
                    v___x_1649_ = v___x_1646_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1642_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_withFreshUsedTheorems___boxed(
    mut v_00_u03b1_1656_: *mut LeanObject,
    mut v_x_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_a_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
    mut v_a_1662_: *mut LeanObject,
    mut v_a_1663_: *mut LeanObject,
    mut v_a_1664_: *mut LeanObject,
    mut v_a_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1666_: *mut LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_Meta_Simp_withFreshUsedTheorems(
        v_00_u03b1_1656_,
        v_x_1657_,
        v_a_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
        v_a_1663_,
        v_a_1664_,
    );
    lean_dec(v_a_1664_);
    lean_dec_ref(v_a_1663_);
    lean_dec(v_a_1662_);
    lean_dec_ref(v_a_1661_);
    lean_dec(v_a_1660_);
    lean_dec_ref(v_a_1659_);
    lean_dec(v_a_1658_);
    return v_res_1666_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__0;
    v___x_1669_ = l_Lean_stringToMessageData(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__2;
    v___x_1672_ = l_Lean_stringToMessageData(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__4;
    v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(
    mut v_x_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_post_1679_: u8 = 0;
    let mut v_inv_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v_r_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut v_ref_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1676_) {
                0 => {
                    v_declName_1678_ = lean_ctor_get(v_x_1676_, 0);
                    lean_inc(v_declName_1678_);
                    v_post_1679_ = lean_ctor_get_uint8(
                        v_x_1676_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_inv_1680_ = lean_ctor_get_uint8(
                        v_x_1676_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1681_ = 0;
                    v_r_1682_ = l_Lean_MessageData_ofConstName(v_declName_1678_, v___x_1681_);
                    if v_post_1679_ == 0 {
                        if v_inv_1680_ == 0 {
                            v___x_1683_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
                            v___x_1684_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                            lean_ctor_set(v___x_1684_, 1, v_r_1682_);
                            v___x_1685_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1685_, 0, v___x_1684_);
                            return v___x_1685_;
                        } else {
                            v___x_1686_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
                            v___x_1687_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1687_, 0, v___x_1686_);
                            lean_ctor_set(v___x_1687_, 1, v_r_1682_);
                            v___x_1688_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1688_, 0, v___x_1687_);
                            return v___x_1688_;
                        }
                    } else {
                        if v_inv_1680_ == 0 {
                            v___x_1689_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1689_, 0, v_r_1682_);
                            return v___x_1689_;
                        } else {
                            v___x_1690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
                            v___x_1691_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1691_, 0, v___x_1690_);
                            lean_ctor_set(v___x_1691_, 1, v_r_1682_);
                            v___x_1692_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                            return v___x_1692_;
                        }
                    }
                }
                1 => {
                    v_fvarId_1693_ = lean_ctor_get(v_x_1676_, 0);
                    v_isSharedCheck_1702_ = (!lean_is_exclusive(v_x_1676_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1695_ = v_x_1676_;
                        v_isShared_1696_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_1693_);
                        lean_dec(v_x_1676_);
                        v___x_1695_ = lean_box(0);
                        v_isShared_1696_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ref_1703_ = lean_ctor_get(v_x_1676_, 1);
                    lean_inc(v_ref_1703_);
                    lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1704_ = l_Lean_MessageData_ofSyntax(v_ref_1703_);
                    v___x_1705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1705_, 0, v___x_1704_);
                    return v___x_1705_;
                }
                _ => {
                    v_name_1706_ = lean_ctor_get(v_x_1676_, 0);
                    v_isSharedCheck_1714_ = (!lean_is_exclusive(v_x_1676_)) as u8;
                    if v_isSharedCheck_1714_ == 0 {
                        v___x_1708_ = v_x_1676_;
                        v_isShared_1709_ = v_isSharedCheck_1714_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_name_1706_);
                        lean_dec(v_x_1676_);
                        v___x_1708_ = lean_box(0);
                        v_isShared_1709_ = v_isSharedCheck_1714_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1697_ = l_Lean_mkFVar(v_fvarId_1693_);
                v___x_1698_ = l_Lean_MessageData_ofExpr(v___x_1697_);
                if v_isShared_1696_ == 0 {
                    lean_ctor_set_tag(v___x_1695_, 0);
                    lean_ctor_set(v___x_1695_, 0, v___x_1698_);
                    v___x_1700_ = v___x_1695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1700_;
            }
            3 => {
                v___x_1710_ = l_Lean_MessageData_ofName(v_name_1706_);
                if v_isShared_1709_ == 0 {
                    lean_ctor_set_tag(v___x_1708_, 0);
                    lean_ctor_set(v___x_1708_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___boxed(
    mut v_x_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1717_: *mut LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_1715_);
    return v_res_1717_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(
    mut v_x_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_x_1718_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___boxed(
    mut v_x_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1731_: *mut LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
    lean_dec(v___y_1729_);
    lean_dec_ref(v___y_1728_);
    lean_dec(v___y_1727_);
    lean_dec_ref(v___y_1726_);
    return v_res_1731_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__0;
    v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
    return v___x_1734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(
    mut v_sz_1735_: usize,
    mut v_i_1736_: usize,
    mut v_bs_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: usize = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1743_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
                if v___x_1743_ == 0 {
                    v___x_1744_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1744_, 0, v_bs_1737_);
                    return v___x_1744_;
                } else {
                    v_v_1745_ = lean_array_uget(v_bs_1737_, v_i_1736_);
                    v___x_1746_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1747_ = lean_array_uset(v_bs_1737_, v_i_1736_, v___x_1746_);
                    v___x_1754_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg(v_v_1745_);
                    if lean_obj_tag(v___x_1754_) == 0 {
                        v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
                        lean_inc(v_a_1755_);
                        lean_dec_ref_known(v___x_1754_, 1);
                        v___x_1756_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
                        v___x_1757_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                        lean_ctor_set(v___x_1757_, 1, v_a_1755_);
                        v___x_1758_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1758_, 0, v___x_1757_);
                        lean_ctor_set(v___x_1758_, 1, v___x_1756_);
                        v_a_1749_ = v___x_1758_;
                        state = 1;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_1754_) == 0 {
                            v_a_1759_ = lean_ctor_get(v___x_1754_, 0);
                            lean_inc(v_a_1759_);
                            lean_dec_ref_known(v___x_1754_, 1);
                            v_a_1749_ = v_a_1759_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_bs_x27_1747_);
                            v_a_1760_ = lean_ctor_get(v___x_1754_, 0);
                            v_isSharedCheck_1767_ = (!lean_is_exclusive(v___x_1754_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v___x_1762_ = v___x_1754_;
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1760_);
                                lean_dec(v___x_1754_);
                                v___x_1762_ = lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1750_ = 1usize;
                v___x_1751_ = lean_usize_add(v_i_1736_, v___x_1750_);
                v___x_1752_ = lean_array_uset(v_bs_x27_1747_, v_i_1736_, v_a_1749_);
                v_i_1736_ = v___x_1751_;
                v_bs_1737_ = v___x_1752_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1763_ == 0 {
                    v___x_1765_ = v___x_1762_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___boxed(
    mut v_sz_1768_: *mut LeanObject,
    mut v_i_1769_: *mut LeanObject,
    mut v_bs_1770_: *mut LeanObject,
    mut v___y_1771_: *mut LeanObject,
    mut v___y_1772_: *mut LeanObject,
    mut v___y_1773_: *mut LeanObject,
    mut v___y_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1776_: usize = 0;
    let mut v_i_boxed_1777_: usize = 0;
    let mut v_res_1778_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1768_);
    lean_dec(v_sz_1768_);
    v_i_boxed_1777_ = lean_unbox_usize(v_i_1769_);
    lean_dec(v_i_1769_);
    v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_boxed_1776_, v_i_boxed_1777_, v_bs_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
    lean_dec(v___y_1774_);
    lean_dec_ref(v___y_1773_);
    lean_dec(v___y_1772_);
    lean_dec_ref(v___y_1771_);
    return v_res_1778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(
    mut v_origins_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
    mut v_a_1781_: *mut LeanObject,
    mut v_a_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_a_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1785_ = lean_array_size(v_origins_1779_);
                v___x_1786_ = 0usize;
                v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1(v_sz_1785_, v___x_1786_, v_origins_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
                if lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1797_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1790_ = v___x_1787_;
                        v_isShared_1791_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1788_);
                        lean_dec(v___x_1787_);
                        v___x_1790_ = lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1797_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1798_ = lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1805_ = (!lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v___x_1800_ = v___x_1787_;
                        v_isShared_1801_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1798_);
                        lean_dec(v___x_1787_);
                        v___x_1800_ = lean_box(0);
                        v_isShared_1801_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1792_ = lean_array_to_list(v_a_1788_);
                v___x_1793_ = l_Lean_MessageData_andList(v___x_1792_);
                if v_isShared_1791_ == 0 {
                    lean_ctor_set(v___x_1790_, 0, v___x_1793_);
                    v___x_1795_ = v___x_1790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1795_;
            }
            3 => {
                if v_isShared_1801_ == 0 {
                    v___x_1803_ = v___x_1800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins___boxed(
    mut v_origins_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(
        v_origins_1806_,
        v_a_1807_,
        v_a_1808_,
        v_a_1809_,
        v_a_1810_,
    );
    lean_dec(v_a_1810_);
    lean_dec_ref(v_a_1809_);
    lean_dec(v_a_1808_);
    lean_dec_ref(v_a_1807_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(
    mut v_x_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_post_1816_: u8 = 0;
    let mut v_inv_1817_: u8 = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v_r_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_ref_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1813_) {
                0 => {
                    v_declName_1815_ = lean_ctor_get(v_x_1813_, 0);
                    lean_inc(v_declName_1815_);
                    v_post_1816_ = lean_ctor_get_uint8(
                        v_x_1813_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_inv_1817_ = lean_ctor_get_uint8(
                        v_x_1813_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    lean_dec_ref_known(v_x_1813_, 1);
                    v___x_1818_ = 0;
                    v_r_1819_ = l_Lean_MessageData_ofConstName(v_declName_1815_, v___x_1818_);
                    if v_post_1816_ == 0 {
                        if v_inv_1817_ == 0 {
                            v___x_1820_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__1);
                            v___x_1821_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                            lean_ctor_set(v___x_1821_, 1, v_r_1819_);
                            v___x_1822_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1822_, 0, v___x_1821_);
                            return v___x_1822_;
                        } else {
                            v___x_1823_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__3);
                            v___x_1824_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1824_, 0, v___x_1823_);
                            lean_ctor_set(v___x_1824_, 1, v_r_1819_);
                            v___x_1825_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1825_, 0, v___x_1824_);
                            return v___x_1825_;
                        }
                    } else {
                        if v_inv_1817_ == 0 {
                            v___x_1826_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1826_, 0, v_r_1819_);
                            return v___x_1826_;
                        } else {
                            v___x_1827_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5_once), _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__0___redArg___closed__5);
                            v___x_1828_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1828_, 0, v___x_1827_);
                            lean_ctor_set(v___x_1828_, 1, v_r_1819_);
                            v___x_1829_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1829_, 0, v___x_1828_);
                            return v___x_1829_;
                        }
                    }
                }
                1 => {
                    v_fvarId_1830_ = lean_ctor_get(v_x_1813_, 0);
                    v_isSharedCheck_1839_ = (!lean_is_exclusive(v_x_1813_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1832_ = v_x_1813_;
                        v_isShared_1833_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_1830_);
                        lean_dec(v_x_1813_);
                        v___x_1832_ = lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1839_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_ref_1840_ = lean_ctor_get(v_x_1813_, 1);
                    lean_inc(v_ref_1840_);
                    lean_dec_ref_known(v_x_1813_, 2);
                    v___x_1841_ = l_Lean_MessageData_ofSyntax(v_ref_1840_);
                    v___x_1842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1842_, 0, v___x_1841_);
                    return v___x_1842_;
                }
                _ => {
                    v_name_1843_ = lean_ctor_get(v_x_1813_, 0);
                    v_isSharedCheck_1851_ = (!lean_is_exclusive(v_x_1813_)) as u8;
                    if v_isSharedCheck_1851_ == 0 {
                        v___x_1845_ = v_x_1813_;
                        v_isShared_1846_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_name_1843_);
                        lean_dec(v_x_1813_);
                        v___x_1845_ = lean_box(0);
                        v_isShared_1846_ = v_isSharedCheck_1851_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1834_ = l_Lean_mkFVar(v_fvarId_1830_);
                v___x_1835_ = l_Lean_MessageData_ofExpr(v___x_1834_);
                if v_isShared_1833_ == 0 {
                    lean_ctor_set_tag(v___x_1832_, 0);
                    lean_ctor_set(v___x_1832_, 0, v___x_1835_);
                    v___x_1837_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1837_;
            }
            3 => {
                v___x_1847_ = l_Lean_MessageData_ofName(v_name_1843_);
                if v_isShared_1846_ == 0 {
                    lean_ctor_set_tag(v___x_1845_, 0);
                    lean_ctor_set(v___x_1845_, 0, v___x_1847_);
                    v___x_1849_ = v___x_1845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg___boxed(
    mut v_x_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1854_: *mut LeanObject = core::ptr::null_mut();
    v_res_1854_ =
        l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_1852_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(
    mut v_x_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ =
        l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_x_1855_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___boxed(
    mut v_x_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1874_: *mut LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0(
        v_x_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
        v___y_1869_,
        v___y_1870_,
        v___y_1871_,
        v___y_1872_,
    );
    lean_dec(v___y_1872_);
    lean_dec_ref(v___y_1871_);
    lean_dec(v___y_1870_);
    lean_dec_ref(v___y_1869_);
    lean_dec(v___y_1868_);
    lean_dec_ref(v___y_1867_);
    lean_dec(v___y_1866_);
    return v_res_1874_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(
    mut v___x_1875_: *mut LeanObject,
    mut v_as_1876_: *mut LeanObject,
    mut v_sz_1877_: usize,
    mut v_i_1878_: usize,
    mut v_b_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: usize = 0;
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: u8 = 0;
    let mut v_declName_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_1894_: u8 = 0;
    let mut v_declName_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inv_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1886_ = lean_usize_dec_lt(v_i_1878_, v_sz_1877_);
                if v___x_1886_ == 0 {
                    v___x_1887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1887_, 0, v_b_1879_);
                    return v___x_1887_;
                } else {
                    v_a_1888_ = lean_array_uget_borrowed(v_as_1876_, v_i_1878_);
                    if lean_obj_tag(v_a_1888_) == 0 {
                        if lean_obj_tag(v___x_1875_) == 0 {
                            v_declName_1893_ = lean_ctor_get(v_a_1888_, 0);
                            v_inv_1894_ = lean_ctor_get_uint8(
                                v_a_1888_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            );
                            v_declName_1895_ = lean_ctor_get(v___x_1875_, 0);
                            v_inv_1896_ = lean_ctor_get_uint8(
                                v___x_1875_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            );
                            v___x_1897_ = lean_name_eq(v_declName_1893_, v_declName_1895_);
                            if v___x_1897_ == 0 {
                                v___y_1892_ = v___x_1897_;
                                state = 3;
                                continue;
                            } else {
                                if v_inv_1894_ == 0 {
                                    if v_inv_1896_ == 0 {
                                        v___y_1892_ = v___x_1897_;
                                        state = 3;
                                        continue;
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1892_ = v_inv_1896_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_1875_) == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_1898_ = l_Lean_Meta_Origin_key(v_a_1888_);
                            v___x_1899_ = l_Lean_Meta_Origin_key(v___x_1875_);
                            v___x_1900_ = lean_name_eq(v___x_1898_, v___x_1899_);
                            lean_dec(v___x_1899_);
                            lean_dec(v___x_1898_);
                            v___y_1892_ = v___x_1900_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1883_ = 1usize;
                v___x_1884_ = lean_usize_add(v_i_1878_, v___x_1883_);
                v_i_1878_ = v___x_1884_;
                v_b_1879_ = v_a_1882_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_a_1888_);
                v___x_1890_ = lean_array_push(v_b_1879_, v_a_1888_);
                v_a_1882_ = v___x_1890_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_1892_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v_a_1882_ = v_b_1879_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg___boxed(
    mut v___x_1901_: *mut LeanObject,
    mut v_as_1902_: *mut LeanObject,
    mut v_sz_1903_: *mut LeanObject,
    mut v_i_1904_: *mut LeanObject,
    mut v_b_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1907_: usize = 0;
    let mut v_i_boxed_1908_: usize = 0;
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1907_ = lean_unbox_usize(v_sz_1903_);
    lean_dec(v_sz_1903_);
    v_i_boxed_1908_ = lean_unbox_usize(v_i_1904_);
    lean_dec(v_i_1904_);
    v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_1901_, v_as_1902_, v_sz_boxed_1907_, v_i_boxed_1908_, v_b_1905_);
    lean_dec_ref(v_as_1902_);
    lean_dec_ref(v___x_1901_);
    return v_res_1909_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1() -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__0;
    v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2() -> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1_once),
        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__1,
    );
    v___x_1914_ = l_Lean_MessageData_hint_x27(v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5() -> *mut LeanObject {
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_1919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1918_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
    v_msg_1919_ = l_Lean_stringToMessageData(v___x_1918_);
    return v_msg_1919_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7() -> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__6;
    v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9() -> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__8;
    v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn l_Lean_Meta_Simp_mkLoopWarningMsg(
    mut v_thm_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
    mut v_a_1930_: *mut LeanObject,
    mut v_a_1931_: *mut LeanObject,
    mut v_a_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1948_: usize = 0;
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_origin_1940_ = lean_ctor_get(v_thm_1926_, 4);
                lean_inc_ref_n(v_origin_1940_, 2);
                lean_dec_ref(v_thm_1926_);
                v___x_1941_ =
                    l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(
                        v_origin_1940_,
                    );
                v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
                lean_inc(v_a_1942_);
                lean_dec_ref(v___x_1941_);
                v___x_1943_ = lean_st_ref_get(v_a_1929_);
                v_usedTheorems_1944_ = lean_ctor_get(v___x_1943_, 3);
                lean_inc_ref(v_usedTheorems_1944_);
                lean_dec(v___x_1943_);
                v___x_1945_ = lean_unsigned_to_nat(0);
                v___x_1946_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__3;
                v___x_1947_ = l_Lean_Meta_Simp_UsedSimps_toArray(v_usedTheorems_1944_);
                lean_dec_ref(v_usedTheorems_1944_);
                v_sz_1948_ = lean_array_size(v___x_1947_);
                v___x_1949_ = 0usize;
                v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v_origin_1940_, v___x_1947_, v_sz_1948_, v___x_1949_, v___x_1946_);
                lean_dec_ref(v___x_1947_);
                lean_dec_ref(v_origin_1940_);
                if lean_obj_tag(v___x_1950_) == 0 {
                    v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
                    lean_inc(v_a_1951_);
                    lean_dec_ref_known(v___x_1950_, 1);
                    v_msg_1952_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5_once),
                        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__5,
                    );
                    v___x_1953_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7_once),
                        _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__7,
                    );
                    v___x_1954_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                    lean_ctor_set(v___x_1954_, 1, v_a_1942_);
                    v___x_1955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins_spec__1___closed__1);
                    v___x_1956_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1956_, 0, v___x_1954_);
                    lean_ctor_set(v___x_1956_, 1, v___x_1955_);
                    v___x_1957_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1957_, 0, v_msg_1952_);
                    lean_ctor_set(v___x_1957_, 1, v___x_1956_);
                    v___x_1958_ = lean_array_get_size(v_a_1951_);
                    v___x_1959_ = lean_nat_dec_eq(v___x_1958_, v___x_1945_);
                    if v___x_1959_ == 0 {
                        v___x_1960_ = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_ppOrigins(v_a_1951_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
                        if lean_obj_tag(v___x_1960_) == 0 {
                            v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
                            lean_inc(v_a_1961_);
                            lean_dec_ref_known(v___x_1960_, 1);
                            v___x_1962_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9_once
                                ),
                                _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__9,
                            );
                            v___x_1963_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                            lean_ctor_set(v___x_1963_, 1, v_a_1961_);
                            v___x_1964_ = l_Lean_MessageData_note(v___x_1963_);
                            v___x_1965_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1965_, 0, v___x_1957_);
                            lean_ctor_set(v___x_1965_, 1, v___x_1964_);
                            v_msg_1936_ = v___x_1965_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_1957_, 2);
                            return v___x_1960_;
                        }
                    } else {
                        lean_dec(v_a_1951_);
                        v_msg_1936_ = v___x_1957_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1942_);
                    v_a_1966_ = lean_ctor_get(v___x_1950_, 0);
                    v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1950_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1950_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1966_);
                        lean_dec(v___x_1950_);
                        v___x_1968_ = lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1937_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2_once),
                    _init_l_Lean_Meta_Simp_mkLoopWarningMsg___closed__2,
                );
                v___x_1938_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1938_, 0, v_msg_1936_);
                lean_ctor_set(v___x_1938_, 1, v___x_1937_);
                v___x_1939_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                return v___x_1939_;
            }
            2 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_mkLoopWarningMsg___boxed(
    mut v_thm_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1983_: *mut LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
        v_thm_1974_,
        v_a_1975_,
        v_a_1976_,
        v_a_1977_,
        v_a_1978_,
        v_a_1979_,
        v_a_1980_,
        v_a_1981_,
    );
    lean_dec(v_a_1981_);
    lean_dec_ref(v_a_1980_);
    lean_dec(v_a_1979_);
    lean_dec_ref(v_a_1978_);
    lean_dec(v_a_1977_);
    lean_dec_ref(v_a_1976_);
    lean_dec(v_a_1975_);
    return v_res_1983_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(
    mut v___x_1984_: *mut LeanObject,
    mut v_as_1985_: *mut LeanObject,
    mut v_sz_1986_: usize,
    mut v_i_1987_: usize,
    mut v_b_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___redArg(v___x_1984_, v_as_1985_, v_sz_1986_, v_i_1987_, v_b_1988_);
    return v___x_1997_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1___boxed(
    mut v___x_1998_: *mut LeanObject,
    mut v_as_1999_: *mut LeanObject,
    mut v_sz_2000_: *mut LeanObject,
    mut v_i_2001_: *mut LeanObject,
    mut v_b_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2011_: usize = 0;
    let mut v_i_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2000_);
    lean_dec(v_sz_2000_);
    v_i_boxed_2012_ = lean_unbox_usize(v_i_2001_);
    lean_dec(v_i_2001_);
    v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__1(v___x_1998_, v_as_1999_, v_sz_boxed_2011_, v_i_boxed_2012_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
    lean_dec(v___y_2009_);
    lean_dec_ref(v___y_2008_);
    lean_dec(v___y_2007_);
    lean_dec_ref(v___y_2006_);
    lean_dec(v___y_2005_);
    lean_dec_ref(v___y_2004_);
    lean_dec(v___y_2003_);
    lean_dec_ref(v_as_1999_);
    lean_dec_ref(v___x_1998_);
    return v_res_2013_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(
    mut v_o_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ = lean_st_ref_get(v___y_2015_);
    v_env_2018_ = lean_ctor_get(v___x_2017_, 0);
    lean_inc_ref(v_env_2018_);
    lean_dec(v___x_2017_);
    v___x_2019_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2020_ = lean_ctor_get(v___x_2019_, 0);
    v_asyncMode_2021_ = lean_ctor_get(v_toEnvExtension_2020_, 2);
    v___x_2022_ = lean_box(1);
    v___x_2023_ = lean_box(0);
    v_linterSets_2024_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2022_,
        v___x_2019_,
        v_env_2018_,
        v_asyncMode_2021_,
        v___x_2023_,
    );
    v___x_2025_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2025_, 0, v_o_2014_);
    lean_ctor_set(v___x_2025_, 1, v_linterSets_2024_);
    v___x_2026_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2026_, 0, v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg___boxed(
    mut v_o_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_2027_, v___y_2028_);
    lean_dec(v___y_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(
    mut v___y_2031_: *mut LeanObject,
    mut v___y_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v_options_2034_ = lean_ctor_get(v___y_2031_, 2);
    lean_inc_ref(v_options_2034_);
    v___x_2035_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_options_2034_, v___y_2032_);
    return v___x_2035_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0___boxed(
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2039_: *mut LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(
        v___y_2036_,
        v___y_2037_,
    );
    lean_dec(v___y_2037_);
    lean_dec_ref(v___y_2036_);
    return v_res_2039_;
}
pub unsafe fn l_Lean_Meta_Simp_shouldCheckLoops(
    mut v_force_2040_: u8,
    mut v_ctxt_2041_: *mut LeanObject,
    mut v_a_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_singlePass_2046_: u8 = 0;
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_2045_ = lean_ctor_get(v_ctxt_2041_, 0);
                v_singlePass_2046_ = lean_ctor_get_uint8(
                    v_config_2045_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                if v_singlePass_2046_ == 0 {
                    if v_force_2040_ == 0 {
                        v___x_2047_ = l_Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0(v_a_2042_, v_a_2043_);
                        v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
                        v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_2047_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v___x_2050_ = v___x_2047_;
                            v_isShared_2051_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2048_);
                            lean_dec(v___x_2047_);
                            v___x_2050_ = lean_box(0);
                            v_isShared_2051_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2059_ = lean_box((v_force_2040_) as usize);
                        v___x_2060_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2060_, 0, v___x_2059_);
                        return v___x_2060_;
                    }
                } else {
                    v___x_2061_ = 0;
                    v___x_2062_ = lean_box((v___x_2061_) as usize);
                    v___x_2063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2063_, 0, v___x_2062_);
                    return v___x_2063_;
                }
            }
            1 => {
                v___x_2052_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
                v___x_2053_ = l_Lean_Linter_getLinterValue(v___x_2052_, v_a_2048_);
                lean_dec(v_a_2048_);
                v___x_2054_ = lean_box((v___x_2053_) as usize);
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_shouldCheckLoops___boxed(
    mut v_force_2064_: *mut LeanObject,
    mut v_ctxt_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_force_boxed_2069_: u8 = 0;
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v_force_boxed_2069_ = (lean_unbox(v_force_2064_) as u8);
    v_res_2070_ =
        l_Lean_Meta_Simp_shouldCheckLoops(v_force_boxed_2069_, v_ctxt_2065_, v_a_2066_, v_a_2067_);
    lean_dec(v_a_2067_);
    lean_dec_ref(v_a_2066_);
    lean_dec_ref(v_ctxt_2065_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(
    mut v_o_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___redArg(v_o_2071_, v___y_2073_);
    return v___x_2075_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0___boxed(
    mut v_o_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2080_: *mut LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Meta_Simp_shouldCheckLoops_spec__0_spec__0(v_o_2076_, v___y_2077_, v___y_2078_);
    lean_dec(v___y_2078_);
    lean_dec_ref(v___y_2077_);
    return v_res_2080_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(
    mut v_k_2081_: *mut LeanObject,
    mut v_b_2082_: *mut LeanObject,
    mut v_c_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2087_);
    lean_inc_ref(v___y_2086_);
    lean_inc(v___y_2085_);
    lean_inc_ref(v___y_2084_);
    v___x_2089_ = lean_apply_7(
        v_k_2081_,
        v_b_2082_,
        v_c_2083_,
        v___y_2084_,
        v___y_2085_,
        v___y_2086_,
        v___y_2087_,
        lean_box(0),
    );
    return v___x_2089_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed(
    mut v_k_2090_: *mut LeanObject,
    mut v_b_2091_: *mut LeanObject,
    mut v_c_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2098_: *mut LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0(v_k_2090_, v_b_2091_, v_c_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    return v_res_2098_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
    mut v_type_2099_: *mut LeanObject,
    mut v_k_2100_: *mut LeanObject,
    mut v_cleanupAnnotations_2101_: u8,
    mut v_whnfType_2102_: u8,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut v_a_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2108_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2108_, 0, v_k_2100_);
                v___x_2109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_2099_,
                    v___f_2108_,
                    v_cleanupAnnotations_2101_,
                    v_whnfType_2102_,
                    v___y_2103_,
                    v___y_2104_,
                    v___y_2105_,
                    v___y_2106_,
                );
                if lean_obj_tag(v___x_2109_) == 0 {
                    v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2117_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2117_ == 0 {
                        v___x_2112_ = v___x_2109_;
                        v_isShared_2113_ = v_isSharedCheck_2117_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2110_);
                        lean_dec(v___x_2109_);
                        v___x_2112_ = lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2117_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2118_ = lean_ctor_get(v___x_2109_, 0);
                    v_isSharedCheck_2125_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2120_ = v___x_2109_;
                        v_isShared_2121_ = v_isSharedCheck_2125_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2118_);
                        lean_dec(v___x_2109_);
                        v___x_2120_ = lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2125_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2113_ == 0 {
                    v___x_2115_ = v___x_2112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2115_;
            }
            3 => {
                if v_isShared_2121_ == 0 {
                    v___x_2123_ = v___x_2120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
                    v___x_2123_ = v_reuseFailAlloc_2124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg___boxed(
    mut v_type_2126_: *mut LeanObject,
    mut v_k_2127_: *mut LeanObject,
    mut v_cleanupAnnotations_2128_: *mut LeanObject,
    mut v_whnfType_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2135_: u8 = 0;
    let mut v_whnfType_boxed_2136_: u8 = 0;
    let mut v_res_2137_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2135_ = (lean_unbox(v_cleanupAnnotations_2128_) as u8);
    v_whnfType_boxed_2136_ = (lean_unbox(v_whnfType_2129_) as u8);
    v_res_2137_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
            v_type_2126_,
            v_k_2127_,
            v_cleanupAnnotations_boxed_2135_,
            v_whnfType_boxed_2136_,
            v___y_2130_,
            v___y_2131_,
            v___y_2132_,
            v___y_2133_,
        );
    lean_dec(v___y_2133_);
    lean_dec_ref(v___y_2132_);
    lean_dec(v___y_2131_);
    lean_dec_ref(v___y_2130_);
    return v_res_2137_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(
    mut v_00_u03b1_2138_: *mut LeanObject,
    mut v_type_2139_: *mut LeanObject,
    mut v_k_2140_: *mut LeanObject,
    mut v_cleanupAnnotations_2141_: u8,
    mut v_whnfType_2142_: u8,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(
            v_type_2139_,
            v_k_2140_,
            v_cleanupAnnotations_2141_,
            v_whnfType_2142_,
            v___y_2143_,
            v___y_2144_,
            v___y_2145_,
            v___y_2146_,
        );
    return v___x_2148_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___boxed(
    mut v_00_u03b1_2149_: *mut LeanObject,
    mut v_type_2150_: *mut LeanObject,
    mut v_k_2151_: *mut LeanObject,
    mut v_cleanupAnnotations_2152_: *mut LeanObject,
    mut v_whnfType_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2159_: u8 = 0;
    let mut v_whnfType_boxed_2160_: u8 = 0;
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2159_ = (lean_unbox(v_cleanupAnnotations_2152_) as u8);
    v_whnfType_boxed_2160_ = (lean_unbox(v_whnfType_2153_) as u8);
    v_res_2161_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3(
        v_00_u03b1_2149_,
        v_type_2150_,
        v_k_2151_,
        v_cleanupAnnotations_boxed_2159_,
        v_whnfType_boxed_2160_,
        v___y_2154_,
        v___y_2155_,
        v___y_2156_,
        v___y_2157_,
    );
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    lean_dec(v___y_2155_);
    lean_dec_ref(v___y_2154_);
    return v_res_2161_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(
    mut v_msgData_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_st_ref_get(v___y_2166_);
    v_env_2169_ = lean_ctor_get(v___x_2168_, 0);
    lean_inc_ref(v_env_2169_);
    lean_dec(v___x_2168_);
    v___x_2170_ = lean_st_ref_get(v___y_2164_);
    v_mctx_2171_ = lean_ctor_get(v___x_2170_, 0);
    lean_inc_ref(v_mctx_2171_);
    lean_dec(v___x_2170_);
    v_lctx_2172_ = lean_ctor_get(v___y_2163_, 2);
    v_options_2173_ = lean_ctor_get(v___y_2165_, 2);
    lean_inc_ref(v_options_2173_);
    lean_inc_ref(v_lctx_2172_);
    v___x_2174_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2174_, 0, v_env_2169_);
    lean_ctor_set(v___x_2174_, 1, v_mctx_2171_);
    lean_ctor_set(v___x_2174_, 2, v_lctx_2172_);
    lean_ctor_set(v___x_2174_, 3, v_options_2173_);
    v___x_2175_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2175_, 0, v___x_2174_);
    lean_ctor_set(v___x_2175_, 1, v_msgData_2162_);
    v___x_2176_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    return v___x_2176_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4___boxed(
    mut v_msgData_2177_: *mut LeanObject,
    mut v___y_2178_: *mut LeanObject,
    mut v___y_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2183_: *mut LeanObject = core::ptr::null_mut();
    v_res_2183_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msgData_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
    lean_dec(v___y_2181_);
    lean_dec_ref(v___y_2180_);
    lean_dec(v___y_2179_);
    lean_dec_ref(v___y_2178_);
    return v_res_2183_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: f64 = 0.0;
    v___x_2184_ = lean_unsigned_to_nat(0);
    v___x_2185_ = lean_float_of_nat(v___x_2184_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
    mut v_cls_2188_: *mut LeanObject,
    mut v_msg_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v_tid_2214_: u64 = 0;
    let mut v_traces_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: f64 = 0.0;
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2195_ = lean_ctor_get(v___y_2192_, 5);
                v___x_2196_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
                v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
                v_isSharedCheck_2241_ = (!lean_is_exclusive(v___x_2196_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v___x_2199_ = v___x_2196_;
                    v_isShared_2200_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2197_);
                    lean_dec(v___x_2196_);
                    v___x_2199_ = lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = lean_st_ref_take(v___y_2193_);
                v_traceState_2202_ = lean_ctor_get(v___x_2201_, 4);
                v_env_2203_ = lean_ctor_get(v___x_2201_, 0);
                v_nextMacroScope_2204_ = lean_ctor_get(v___x_2201_, 1);
                v_ngen_2205_ = lean_ctor_get(v___x_2201_, 2);
                v_auxDeclNGen_2206_ = lean_ctor_get(v___x_2201_, 3);
                v_cache_2207_ = lean_ctor_get(v___x_2201_, 5);
                v_messages_2208_ = lean_ctor_get(v___x_2201_, 6);
                v_infoState_2209_ = lean_ctor_get(v___x_2201_, 7);
                v_snapshotTasks_2210_ = lean_ctor_get(v___x_2201_, 8);
                v_isSharedCheck_2240_ = (!lean_is_exclusive(v___x_2201_)) as u8;
                if v_isSharedCheck_2240_ == 0 {
                    v___x_2212_ = v___x_2201_;
                    v_isShared_2213_ = v_isSharedCheck_2240_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2210_);
                    lean_inc(v_infoState_2209_);
                    lean_inc(v_messages_2208_);
                    lean_inc(v_cache_2207_);
                    lean_inc(v_traceState_2202_);
                    lean_inc(v_auxDeclNGen_2206_);
                    lean_inc(v_ngen_2205_);
                    lean_inc(v_nextMacroScope_2204_);
                    lean_inc(v_env_2203_);
                    lean_dec(v___x_2201_);
                    v___x_2212_ = lean_box(0);
                    v_isShared_2213_ = v_isSharedCheck_2240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2214_ = lean_ctor_get_uint64(
                    v_traceState_2202_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2215_ = lean_ctor_get(v_traceState_2202_, 0);
                v_isSharedCheck_2239_ = (!lean_is_exclusive(v_traceState_2202_)) as u8;
                if v_isSharedCheck_2239_ == 0 {
                    v___x_2217_ = v_traceState_2202_;
                    v_isShared_2218_ = v_isSharedCheck_2239_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2215_);
                    lean_dec(v_traceState_2202_);
                    v___x_2217_ = lean_box(0);
                    v_isShared_2218_ = v_isSharedCheck_2239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2219_ = lean_box(0);
                v___x_2220_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__0);
                v___x_2221_ = 0;
                v___x_2222_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
                v___x_2223_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2223_, 0, v_cls_2188_);
                lean_ctor_set(v___x_2223_, 1, v___x_2219_);
                lean_ctor_set(v___x_2223_, 2, v___x_2222_);
                lean_ctor_set_float(
                    v___x_2223_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2220_,
                );
                lean_ctor_set_float(
                    v___x_2223_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2220_,
                );
                lean_ctor_set_uint8(
                    v___x_2223_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2221_,
                );
                v___x_2224_ =
                    l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___closed__1;
                v___x_2225_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2225_, 0, v___x_2223_);
                lean_ctor_set(v___x_2225_, 1, v_a_2197_);
                lean_ctor_set(v___x_2225_, 2, v___x_2224_);
                lean_inc(v_ref_2195_);
                v___x_2226_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2226_, 0, v_ref_2195_);
                lean_ctor_set(v___x_2226_, 1, v___x_2225_);
                v___x_2227_ = l_Lean_PersistentArray_push___redArg(v_traces_2215_, v___x_2226_);
                if v_isShared_2218_ == 0 {
                    lean_ctor_set(v___x_2217_, 0, v___x_2227_);
                    v___x_2229_ = v___x_2217_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2227_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2214_,
                    );
                    v___x_2229_ = v_reuseFailAlloc_2238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2213_ == 0 {
                    lean_ctor_set(v___x_2212_, 4, v___x_2229_);
                    v___x_2231_ = v___x_2212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_env_2203_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_nextMacroScope_2204_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_ngen_2205_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_auxDeclNGen_2206_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 4, v___x_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 5, v_cache_2207_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 6, v_messages_2208_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 7, v_infoState_2209_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 8, v_snapshotTasks_2210_);
                    v___x_2231_ = v_reuseFailAlloc_2237_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2232_ = lean_st_ref_set(v___y_2193_, v___x_2231_);
                v___x_2233_ = lean_box(0);
                if v_isShared_2200_ == 0 {
                    lean_ctor_set(v___x_2199_, 0, v___x_2233_);
                    v___x_2235_ = v___x_2199_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg___boxed(
    mut v_cls_2242_: *mut LeanObject,
    mut v_msg_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2249_: *mut LeanObject = core::ptr::null_mut();
    v_res_2249_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
        v_cls_2242_,
        v_msg_2243_,
        v___y_2244_,
        v___y_2245_,
        v___y_2246_,
        v___y_2247_,
    );
    lean_dec(v___y_2247_);
    lean_dec_ref(v___y_2246_);
    lean_dec(v___y_2245_);
    lean_dec_ref(v___y_2244_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(
    mut v_opts_2250_: *mut LeanObject,
    mut v_opt_2251_: *mut LeanObject,
) -> u8 {
    let mut v_name_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v_name_2252_ = lean_ctor_get(v_opt_2251_, 0);
    v_defValue_2253_ = lean_ctor_get(v_opt_2251_, 1);
    v_map_2254_ = lean_ctor_get(v_opts_2250_, 0);
    v___x_2255_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2254_,
            v_name_2252_,
        );
    if lean_obj_tag(v___x_2255_) == 0 {
        let mut v___x_2256_: u8 = 0;
        v___x_2256_ = (lean_unbox(v_defValue_2253_) as u8);
        return v___x_2256_;
    } else {
        let mut v_val_2257_: *mut LeanObject = core::ptr::null_mut();
        v_val_2257_ = lean_ctor_get(v___x_2255_, 0);
        lean_inc(v_val_2257_);
        lean_dec_ref_known(v___x_2255_, 1);
        if lean_obj_tag(v_val_2257_) == 1 {
            let mut v_v_2258_: u8 = 0;
            v_v_2258_ = lean_ctor_get_uint8(v_val_2257_, 0 as u32);
            lean_dec_ref_known(v_val_2257_, 0);
            return v_v_2258_;
        } else {
            let mut v___x_2259_: u8 = 0;
            lean_dec(v_val_2257_);
            v___x_2259_ = (lean_unbox(v_defValue_2253_) as u8);
            return v___x_2259_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_opts_2260_: *mut LeanObject,
    mut v_opt_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2262_: u8 = 0;
    let mut v_r_2263_: *mut LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_opts_2260_, v_opt_2261_);
    lean_dec_ref(v_opt_2261_);
    lean_dec_ref(v_opts_2260_);
    v_r_2263_ = lean_box((v_res_2262_) as usize);
    return v_r_2263_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v___y_2272_: u8,
    mut v_suppressElabErrors_2273_: u8,
    mut v_x_2274_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2274_) == 1 {
        let mut v_pre_2275_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2275_ = lean_ctor_get(v_x_2274_, 0);
        match lean_obj_tag(v_pre_2275_) {
            1 => {
                let mut v_pre_2276_: *mut LeanObject = core::ptr::null_mut();
                v_pre_2276_ = lean_ctor_get(v_pre_2275_, 0);
                match lean_obj_tag(v_pre_2276_) {
                    0 => {
                        let mut v_str_2277_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_2278_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2280_: u8 = 0;
                        v_str_2277_ = lean_ctor_get(v_x_2274_, 1);
                        v_str_2278_ = lean_ctor_get(v_pre_2275_, 1);
                        v___x_2279_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__0;
                        v___x_2280_ = lean_string_dec_eq(v_str_2278_, v___x_2279_);
                        if v___x_2280_ == 0 {
                            let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2282_: u8 = 0;
                            v___x_2281_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
                            v___x_2282_ = lean_string_dec_eq(v_str_2278_, v___x_2281_);
                            if v___x_2282_ == 0 {
                                return v___y_2272_;
                            } else {
                                let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2284_: u8 = 0;
                                v___x_2283_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__2;
                                v___x_2284_ = lean_string_dec_eq(v_str_2277_, v___x_2283_);
                                if v___x_2284_ == 0 {
                                    return v___y_2272_;
                                } else {
                                    return v_suppressElabErrors_2273_;
                                }
                            }
                        } else {
                            let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2286_: u8 = 0;
                            v___x_2285_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__3;
                            v___x_2286_ = lean_string_dec_eq(v_str_2277_, v___x_2285_);
                            if v___x_2286_ == 0 {
                                return v___y_2272_;
                            } else {
                                return v_suppressElabErrors_2273_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2287_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_2287_ = lean_ctor_get(v_pre_2276_, 0);
                        if lean_obj_tag(v_pre_2287_) == 0 {
                            let mut v_str_2288_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2289_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2290_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2292_: u8 = 0;
                            v_str_2288_ = lean_ctor_get(v_x_2274_, 1);
                            v_str_2289_ = lean_ctor_get(v_pre_2275_, 1);
                            v_str_2290_ = lean_ctor_get(v_pre_2276_, 1);
                            v___x_2291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__4;
                            v___x_2292_ = lean_string_dec_eq(v_str_2290_, v___x_2291_);
                            if v___x_2292_ == 0 {
                                return v___y_2272_;
                            } else {
                                let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2294_: u8 = 0;
                                v___x_2293_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__5;
                                v___x_2294_ = lean_string_dec_eq(v_str_2289_, v___x_2293_);
                                if v___x_2294_ == 0 {
                                    return v___y_2272_;
                                } else {
                                    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_2296_: u8 = 0;
                                    v___x_2295_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__6;
                                    v___x_2296_ = lean_string_dec_eq(v_str_2288_, v___x_2295_);
                                    if v___x_2296_ == 0 {
                                        return v___y_2272_;
                                    } else {
                                        return v_suppressElabErrors_2273_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2272_;
                        }
                    }
                    _ => {
                        return v___y_2272_;
                    }
                }
            }
            0 => {
                let mut v_str_2297_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2299_: u8 = 0;
                v_str_2297_ = lean_ctor_get(v_x_2274_, 1);
                v___x_2298_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___closed__7;
                v___x_2299_ = lean_string_dec_eq(v_str_2297_, v___x_2298_);
                if v___x_2299_ == 0 {
                    return v___y_2272_;
                } else {
                    return v_suppressElabErrors_2273_;
                }
            }
            _ => {
                return v___y_2272_;
            }
        }
    } else {
        return v___y_2272_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed(
    mut v___y_2300_: *mut LeanObject,
    mut v_suppressElabErrors_2301_: *mut LeanObject,
    mut v_x_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_24906__boxed_2303_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2304_: u8 = 0;
    let mut v_res_2305_: u8 = 0;
    let mut v_r_2306_: *mut LeanObject = core::ptr::null_mut();
    v___y_24906__boxed_2303_ = (lean_unbox(v___y_2300_) as u8);
    v_suppressElabErrors_boxed_2304_ = (lean_unbox(v_suppressElabErrors_2301_) as u8);
    v_res_2305_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0(v___y_24906__boxed_2303_, v_suppressElabErrors_boxed_2304_, v_x_2302_);
    lean_dec(v_x_2302_);
    v_r_2306_ = lean_box((v_res_2305_) as usize);
    return v_r_2306_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(
    mut v_ref_2307_: *mut LeanObject,
    mut v_msgData_2308_: *mut LeanObject,
    mut v_severity_2309_: u8,
    mut v_isSilent_2310_: u8,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2318_: u8 = 0;
    let mut v___y_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: u8 = 0;
    let mut v___y_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v___y_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2354_: u8 = 0;
    let mut v___y_2355_: u8 = 0;
    let mut v___y_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: u8 = 0;
    let mut v___y_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v___y_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: u8 = 0;
    let mut v___y_2381_: u8 = 0;
    let mut v___y_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: u8 = 0;
    let mut v___y_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: u8 = 0;
    let mut v___y_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2394_: u8 = 0;
    let mut v___y_2395_: u8 = 0;
    let mut v_ref_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___y_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: u8 = 0;
    let mut v___y_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: u8 = 0;
    let mut v___y_2408_: u8 = 0;
    let mut v___y_2410_: u8 = 0;
    let mut v_fileName_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2415_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2400_ = 2;
                v___x_2425_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2400_);
                if v___x_2425_ == 0 {
                    v___y_2410_ = v___x_2425_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_2308_);
                    v___x_2426_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2308_);
                    v___y_2410_ = v___x_2426_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2326_ = lean_st_ref_take(v___y_2325_);
                v_currNamespace_2327_ = lean_ctor_get(v___y_2324_, 6);
                v_openDecls_2328_ = lean_ctor_get(v___y_2324_, 7);
                v_env_2329_ = lean_ctor_get(v___x_2326_, 0);
                v_nextMacroScope_2330_ = lean_ctor_get(v___x_2326_, 1);
                v_ngen_2331_ = lean_ctor_get(v___x_2326_, 2);
                v_auxDeclNGen_2332_ = lean_ctor_get(v___x_2326_, 3);
                v_traceState_2333_ = lean_ctor_get(v___x_2326_, 4);
                v_cache_2334_ = lean_ctor_get(v___x_2326_, 5);
                v_messages_2335_ = lean_ctor_get(v___x_2326_, 6);
                v_infoState_2336_ = lean_ctor_get(v___x_2326_, 7);
                v_snapshotTasks_2337_ = lean_ctor_get(v___x_2326_, 8);
                v_isSharedCheck_2351_ = (!lean_is_exclusive(v___x_2326_)) as u8;
                if v_isSharedCheck_2351_ == 0 {
                    v___x_2339_ = v___x_2326_;
                    v_isShared_2340_ = v_isSharedCheck_2351_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2337_);
                    lean_inc(v_infoState_2336_);
                    lean_inc(v_messages_2335_);
                    lean_inc(v_cache_2334_);
                    lean_inc(v_traceState_2333_);
                    lean_inc(v_auxDeclNGen_2332_);
                    lean_inc(v_ngen_2331_);
                    lean_inc(v_nextMacroScope_2330_);
                    lean_inc(v_env_2329_);
                    lean_dec(v___x_2326_);
                    v___x_2339_ = lean_box(0);
                    v_isShared_2340_ = v_isSharedCheck_2351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_2328_);
                lean_inc(v_currNamespace_2327_);
                v___x_2341_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2341_, 0, v_currNamespace_2327_);
                lean_ctor_set(v___x_2341_, 1, v_openDecls_2328_);
                v___x_2342_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                lean_ctor_set(v___x_2342_, 1, v___y_2320_);
                lean_inc_ref(v___y_2317_);
                lean_inc_ref(v___y_2323_);
                v___x_2343_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2343_, 0, v___y_2323_);
                lean_ctor_set(v___x_2343_, 1, v___y_2319_);
                lean_ctor_set(v___x_2343_, 2, v___y_2321_);
                lean_ctor_set(v___x_2343_, 3, v___y_2317_);
                lean_ctor_set(v___x_2343_, 4, v___x_2342_);
                lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2322_,
                );
                lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2318_,
                );
                lean_ctor_set_uint8(
                    v___x_2343_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2310_,
                );
                v___x_2344_ = l_Lean_MessageLog_add(v___x_2343_, v_messages_2335_);
                if v_isShared_2340_ == 0 {
                    lean_ctor_set(v___x_2339_, 6, v___x_2344_);
                    v___x_2346_ = v___x_2339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_env_2329_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_nextMacroScope_2330_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_ngen_2331_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_auxDeclNGen_2332_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_traceState_2333_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_cache_2334_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 6, v___x_2344_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 7, v_infoState_2336_);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 8, v_snapshotTasks_2337_);
                    v___x_2346_ = v_reuseFailAlloc_2350_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2347_ = lean_st_ref_set(v___y_2325_, v___x_2346_);
                v___x_2348_ = lean_box(0);
                v___x_2349_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2349_, 0, v___x_2348_);
                return v___x_2349_;
            }
            4 => {
                v___x_2361_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2308_,
                    );
                v___x_2362_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2_spec__4(v___x_2361_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
                v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
                v_isSharedCheck_2376_ = (!lean_is_exclusive(v___x_2362_)) as u8;
                if v_isSharedCheck_2376_ == 0 {
                    v___x_2365_ = v___x_2362_;
                    v_isShared_2366_ = v_isSharedCheck_2376_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_2363_);
                    lean_dec(v___x_2362_);
                    v___x_2365_ = lean_box(0);
                    v_isShared_2366_ = v_isSharedCheck_2376_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_2357_, 2);
                v___x_2367_ = l_Lean_FileMap_toPosition(v___y_2357_, v___y_2356_);
                lean_dec(v___y_2356_);
                v___x_2368_ = l_Lean_FileMap_toPosition(v___y_2357_, v___y_2360_);
                lean_dec(v___y_2360_);
                v___x_2369_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                v___x_2370_ = l_Lean_Meta_Simp_mkLoopWarningMsg___closed__4;
                if v___y_2355_ == 0 {
                    lean_del_object(v___x_2365_);
                    lean_dec_ref(v___y_2353_);
                    v___y_2317_ = v___x_2370_;
                    v___y_2318_ = v___y_2354_;
                    v___y_2319_ = v___x_2367_;
                    v___y_2320_ = v_a_2363_;
                    v___y_2321_ = v___x_2369_;
                    v___y_2322_ = v___y_2359_;
                    v___y_2323_ = v___y_2358_;
                    v___y_2324_ = v___y_2313_;
                    v___y_2325_ = v___y_2314_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2363_);
                    v___x_2371_ = l_Lean_MessageData_hasTag(v___y_2353_, v_a_2363_);
                    if v___x_2371_ == 0 {
                        lean_dec_ref_known(v___x_2369_, 1);
                        lean_dec_ref(v___x_2367_);
                        lean_dec(v_a_2363_);
                        v___x_2372_ = lean_box(0);
                        if v_isShared_2366_ == 0 {
                            lean_ctor_set(v___x_2365_, 0, v___x_2372_);
                            v___x_2374_ = v___x_2365_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
                            v___x_2374_ = v_reuseFailAlloc_2375_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2365_);
                        v___y_2317_ = v___x_2370_;
                        v___y_2318_ = v___y_2354_;
                        v___y_2319_ = v___x_2367_;
                        v___y_2320_ = v_a_2363_;
                        v___y_2321_ = v___x_2369_;
                        v___y_2322_ = v___y_2359_;
                        v___y_2323_ = v___y_2358_;
                        v___y_2324_ = v___y_2313_;
                        v___y_2325_ = v___y_2314_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2374_;
            }
            7 => {
                v___x_2386_ = l_Lean_Syntax_getTailPos_x3f(v___y_2379_, v___y_2383_);
                lean_dec(v___y_2379_);
                if lean_obj_tag(v___x_2386_) == 0 {
                    lean_inc(v___y_2385_);
                    v___y_2353_ = v___y_2378_;
                    v___y_2354_ = v___y_2380_;
                    v___y_2355_ = v___y_2381_;
                    v___y_2356_ = v___y_2385_;
                    v___y_2357_ = v___y_2382_;
                    v___y_2358_ = v___y_2384_;
                    v___y_2359_ = v___y_2383_;
                    v___y_2360_ = v___y_2385_;
                    state = 4;
                    continue;
                } else {
                    v_val_2387_ = lean_ctor_get(v___x_2386_, 0);
                    lean_inc(v_val_2387_);
                    lean_dec_ref_known(v___x_2386_, 1);
                    v___y_2353_ = v___y_2378_;
                    v___y_2354_ = v___y_2380_;
                    v___y_2355_ = v___y_2381_;
                    v___y_2356_ = v___y_2385_;
                    v___y_2357_ = v___y_2382_;
                    v___y_2358_ = v___y_2384_;
                    v___y_2359_ = v___y_2383_;
                    v___y_2360_ = v_val_2387_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2396_ = l_Lean_replaceRef(v_ref_2307_, v___y_2391_);
                v___x_2397_ = l_Lean_Syntax_getPos_x3f(v_ref_2396_, v___y_2394_);
                if lean_obj_tag(v___x_2397_) == 0 {
                    v___x_2398_ = lean_unsigned_to_nat(0);
                    v___y_2378_ = v___y_2389_;
                    v___y_2379_ = v_ref_2396_;
                    v___y_2380_ = v___y_2395_;
                    v___y_2381_ = v___y_2390_;
                    v___y_2382_ = v___y_2392_;
                    v___y_2383_ = v___y_2394_;
                    v___y_2384_ = v___y_2393_;
                    v___y_2385_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_val_2399_ = lean_ctor_get(v___x_2397_, 0);
                    lean_inc(v_val_2399_);
                    lean_dec_ref_known(v___x_2397_, 1);
                    v___y_2378_ = v___y_2389_;
                    v___y_2379_ = v_ref_2396_;
                    v___y_2380_ = v___y_2395_;
                    v___y_2381_ = v___y_2390_;
                    v___y_2382_ = v___y_2392_;
                    v___y_2383_ = v___y_2394_;
                    v___y_2384_ = v___y_2393_;
                    v___y_2385_ = v_val_2399_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2408_ == 0 {
                    v___y_2389_ = v___y_2405_;
                    v___y_2390_ = v___y_2403_;
                    v___y_2391_ = v___y_2402_;
                    v___y_2392_ = v___y_2404_;
                    v___y_2393_ = v___y_2406_;
                    v___y_2394_ = v___y_2407_;
                    v___y_2395_ = v_severity_2309_;
                    state = 8;
                    continue;
                } else {
                    v___y_2389_ = v___y_2405_;
                    v___y_2390_ = v___y_2403_;
                    v___y_2391_ = v___y_2402_;
                    v___y_2392_ = v___y_2404_;
                    v___y_2393_ = v___y_2406_;
                    v___y_2394_ = v___y_2407_;
                    v___y_2395_ = v___x_2400_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2410_ == 0 {
                    v_fileName_2411_ = lean_ctor_get(v___y_2313_, 0);
                    v_fileMap_2412_ = lean_ctor_get(v___y_2313_, 1);
                    v_options_2413_ = lean_ctor_get(v___y_2313_, 2);
                    v_ref_2414_ = lean_ctor_get(v___y_2313_, 5);
                    v_suppressElabErrors_2415_ = lean_ctor_get_uint8(
                        v___y_2313_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2416_ = lean_box((v___y_2410_) as usize);
                    v___x_2417_ = lean_box((v_suppressElabErrors_2415_) as usize);
                    v___f_2418_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2418_, 0, v___x_2416_);
                    lean_closure_set(v___f_2418_, 1, v___x_2417_);
                    v___x_2419_ = 1;
                    v___x_2420_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2309_, v___x_2419_);
                    if v___x_2420_ == 0 {
                        v___y_2402_ = v_ref_2414_;
                        v___y_2403_ = v_suppressElabErrors_2415_;
                        v___y_2404_ = v_fileMap_2412_;
                        v___y_2405_ = v___f_2418_;
                        v___y_2406_ = v_fileName_2411_;
                        v___y_2407_ = v___y_2410_;
                        v___y_2408_ = v___x_2420_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2421_ = l_Lean_warningAsError;
                        v___x_2422_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2_spec__6(v_options_2413_, v___x_2421_);
                        v___y_2402_ = v_ref_2414_;
                        v___y_2403_ = v_suppressElabErrors_2415_;
                        v___y_2404_ = v_fileMap_2412_;
                        v___y_2405_ = v___f_2418_;
                        v___y_2406_ = v_fileName_2411_;
                        v___y_2407_ = v___y_2410_;
                        v___y_2408_ = v___x_2422_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_2308_);
                    v___x_2423_ = lean_box(0);
                    v___x_2424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2424_, 0, v___x_2423_);
                    return v___x_2424_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_2427_: *mut LeanObject,
    mut v_msgData_2428_: *mut LeanObject,
    mut v_severity_2429_: *mut LeanObject,
    mut v_isSilent_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2436_: u8 = 0;
    let mut v_isSilent_boxed_2437_: u8 = 0;
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2436_ = (lean_unbox(v_severity_2429_) as u8);
    v_isSilent_boxed_2437_ = (lean_unbox(v_isSilent_2430_) as u8);
    v_res_2438_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2427_, v_msgData_2428_, v_severity_boxed_2436_, v_isSilent_boxed_2437_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
    lean_dec(v___y_2434_);
    lean_dec_ref(v___y_2433_);
    lean_dec(v___y_2432_);
    lean_dec_ref(v___y_2431_);
    lean_dec(v_ref_2427_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(
    mut v_ref_2439_: *mut LeanObject,
    mut v_msgData_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
    mut v___y_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
    mut v___y_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2449_: u8 = 0;
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2449_ = 1;
    v___x_2450_ = 0;
    v___x_2451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2439_, v_msgData_2440_, v___x_2449_, v___x_2450_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
    return v___x_2451_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0___boxed(
    mut v_ref_2452_: *mut LeanObject,
    mut v_msgData_2453_: *mut LeanObject,
    mut v___y_2454_: *mut LeanObject,
    mut v___y_2455_: *mut LeanObject,
    mut v___y_2456_: *mut LeanObject,
    mut v___y_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
    mut v___y_2460_: *mut LeanObject,
    mut v___y_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2462_: *mut LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_ref_2452_, v_msgData_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
    lean_dec(v___y_2460_);
    lean_dec_ref(v___y_2459_);
    lean_dec(v___y_2458_);
    lean_dec_ref(v___y_2457_);
    lean_dec(v___y_2456_);
    lean_dec_ref(v___y_2455_);
    lean_dec(v___y_2454_);
    lean_dec(v_ref_2452_);
    return v_res_2462_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__0;
    v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
    return v___x_2465_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__2;
    v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
    mut v_linterOption_2469_: *mut LeanObject,
    mut v_stx_2470_: *mut LeanObject,
    mut v_msg_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut v_unused_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2480_ = lean_ctor_get(v_linterOption_2469_, 0);
                v_isSharedCheck_2497_ = (!lean_is_exclusive(v_linterOption_2469_)) as u8;
                if v_isSharedCheck_2497_ == 0 {
                    v_unused_2498_ = lean_ctor_get(v_linterOption_2469_, 1);
                    lean_dec(v_unused_2498_);
                    v___x_2482_ = v_linterOption_2469_;
                    v_isShared_2483_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_2480_);
                    lean_dec(v_linterOption_2469_);
                    v___x_2482_ = lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2484_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__1);
                lean_inc(v_name_2480_);
                v___x_2485_ = l_Lean_MessageData_ofName(v_name_2480_);
                if v_isShared_2483_ == 0 {
                    lean_ctor_set_tag(v___x_2482_, 7);
                    lean_ctor_set(v___x_2482_, 1, v___x_2485_);
                    lean_ctor_set(v___x_2482_, 0, v___x_2484_);
                    v___x_2487_ = v___x_2482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2484_);
                    lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2485_);
                    v___x_2487_ = v_reuseFailAlloc_2496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2488_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___closed__3);
                v___x_2489_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2489_, 0, v___x_2487_);
                lean_ctor_set(v___x_2489_, 1, v___x_2488_);
                v_disable_2490_ = l_Lean_MessageData_note(v___x_2489_);
                v___x_2491_ = l_Lean_Linter_linterMessageTag;
                v___x_2492_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2492_, 0, v_msg_2471_);
                lean_ctor_set(v___x_2492_, 1, v_disable_2490_);
                v___x_2493_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2493_, 0, v___x_2491_);
                lean_ctor_set(v___x_2493_, 1, v___x_2492_);
                v___x_2494_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2494_, 0, v_name_2480_);
                lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                v___x_2495_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0(v_stx_2470_, v___x_2494_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0___boxed(
    mut v_linterOption_2499_: *mut LeanObject,
    mut v_stx_2500_: *mut LeanObject,
    mut v_msg_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2510_: *mut LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
        v_linterOption_2499_,
        v_stx_2500_,
        v_msg_2501_,
        v___y_2502_,
        v___y_2503_,
        v___y_2504_,
        v___y_2505_,
        v___y_2506_,
        v___y_2507_,
        v___y_2508_,
    );
    lean_dec(v___y_2508_);
    lean_dec_ref(v___y_2507_);
    lean_dec(v___y_2506_);
    lean_dec_ref(v___y_2505_);
    lean_dec(v___y_2504_);
    lean_dec_ref(v___y_2503_);
    lean_dec(v___y_2502_);
    lean_dec(v_stx_2500_);
    return v_res_2510_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
    mut v_msgData_2511_: *mut LeanObject,
    mut v_severity_2512_: u8,
    mut v_isSilent_2513_: u8,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2522_ = lean_ctor_get(v___y_2519_, 5);
    v___x_2523_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2522_, v_msgData_2511_, v_severity_2512_, v_isSilent_2513_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
    return v___x_2523_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2___boxed(
    mut v_msgData_2524_: *mut LeanObject,
    mut v_severity_2525_: *mut LeanObject,
    mut v_isSilent_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2535_: u8 = 0;
    let mut v_isSilent_boxed_2536_: u8 = 0;
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2535_ = (lean_unbox(v_severity_2525_) as u8);
    v_isSilent_boxed_2536_ = (lean_unbox(v_isSilent_2526_) as u8);
    v_res_2537_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
            v_msgData_2524_,
            v_severity_boxed_2535_,
            v_isSilent_boxed_2536_,
            v___y_2527_,
            v___y_2528_,
            v___y_2529_,
            v___y_2530_,
            v___y_2531_,
            v___y_2532_,
            v___y_2533_,
        );
    lean_dec(v___y_2533_);
    lean_dec_ref(v___y_2532_);
    lean_dec(v___y_2531_);
    lean_dec_ref(v___y_2530_);
    lean_dec(v___y_2529_);
    lean_dec_ref(v___y_2528_);
    lean_dec(v___y_2527_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
    mut v_msgData_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = 1;
    v___x_2548_ = 0;
    v___x_2549_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1_spec__2(
            v_msgData_2538_,
            v___x_2547_,
            v___x_2548_,
            v___y_2539_,
            v___y_2540_,
            v___y_2541_,
            v___y_2542_,
            v___y_2543_,
            v___y_2544_,
            v___y_2545_,
        );
    return v___x_2549_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1___boxed(
    mut v_msgData_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
    mut v___y_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2559_: *mut LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
        v_msgData_2550_,
        v___y_2551_,
        v___y_2552_,
        v___y_2553_,
        v___y_2554_,
        v___y_2555_,
        v___y_2556_,
        v___y_2557_,
    );
    lean_dec(v___y_2557_);
    lean_dec_ref(v___y_2556_);
    lean_dec(v___y_2555_);
    lean_dec_ref(v___y_2554_);
    lean_dec(v___y_2553_);
    lean_dec_ref(v___y_2552_);
    lean_dec(v___y_2551_);
    return v_res_2559_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___x_2569_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__2;
    v___x_2570_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__3;
    v___x_2571_ = l_Lean_Name_append(v___x_2570_, v___x_2569_);
    return v___x_2571_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    v___x_2573_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__5;
    v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__7;
    v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
    return v___x_2577_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__0(
    mut v___x_2578_: *mut LeanObject,
    mut v_force_2579_: u8,
    mut v_thm_2580_: *mut LeanObject,
    mut v_origin_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
    mut v___y_2583_: *mut LeanObject,
    mut v___y_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
    mut v___y_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2630_: u8 = 0;
    let mut v_unused_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v___x_2636_: u8 = 0;
    let mut v_options_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2638_: u8 = 0;
    let mut v_inheritedTraceOptions_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2588_);
                lean_inc_ref(v___y_2587_);
                lean_inc(v___y_2586_);
                lean_inc_ref(v___y_2585_);
                lean_inc(v___y_2584_);
                lean_inc_ref(v___y_2583_);
                lean_inc(v___y_2582_);
                v___x_2622_ = lean_simp(
                    v___x_2578_,
                    v___y_2582_,
                    v___y_2583_,
                    v___y_2584_,
                    v___y_2585_,
                    v___y_2586_,
                    v___y_2587_,
                    v___y_2588_,
                );
                if lean_obj_tag(v___x_2622_) == 0 {
                    lean_dec(v___y_2582_);
                    lean_dec_ref(v_origin_2581_);
                    lean_dec_ref(v_thm_2580_);
                    v_isSharedCheck_2630_ = (!lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2630_ == 0 {
                        v_unused_2631_ = lean_ctor_get(v___x_2622_, 0);
                        lean_dec(v_unused_2631_);
                        v___x_2624_ = v___x_2622_;
                        v_isShared_2625_ = v_isSharedCheck_2630_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_2622_);
                        v___x_2624_ = lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2630_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_2632_ = lean_ctor_get(v___x_2622_, 0);
                    v_isSharedCheck_2656_ = (!lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2634_ = v___x_2622_;
                        v_isShared_2635_ = v_isSharedCheck_2656_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2632_);
                        lean_dec(v___x_2622_);
                        v___x_2634_ = lean_box(0);
                        v_isShared_2635_ = v_isSharedCheck_2656_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if v_force_2579_ == 0 {
                    v___x_2598_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
                        v_thm_2580_,
                        v___y_2591_,
                        v___y_2592_,
                        v___y_2593_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if lean_obj_tag(v___x_2598_) == 0 {
                        v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
                        lean_inc(v_a_2599_);
                        lean_dec_ref_known(v___x_2598_, 1);
                        v_ref_2600_ = lean_ctor_get(v___y_2596_, 5);
                        v___x_2601_ = l_Lean_Meta_Simp_linter_loopingSimpArgs;
                        v___x_2602_ =
                            l_Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0(
                                v___x_2601_,
                                v_ref_2600_,
                                v_a_2599_,
                                v___y_2591_,
                                v___y_2592_,
                                v___y_2593_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                        lean_dec(v___y_2591_);
                        return v___x_2602_;
                    } else {
                        lean_dec(v___y_2591_);
                        v_a_2603_ = lean_ctor_get(v___x_2598_, 0);
                        v_isSharedCheck_2610_ = (!lean_is_exclusive(v___x_2598_)) as u8;
                        if v_isSharedCheck_2610_ == 0 {
                            v___x_2605_ = v___x_2598_;
                            v_isShared_2606_ = v_isSharedCheck_2610_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2603_);
                            lean_dec(v___x_2598_);
                            v___x_2605_ = lean_box(0);
                            v_isShared_2606_ = v_isSharedCheck_2610_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2611_ = l_Lean_Meta_Simp_mkLoopWarningMsg(
                        v_thm_2580_,
                        v___y_2591_,
                        v___y_2592_,
                        v___y_2593_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if lean_obj_tag(v___x_2611_) == 0 {
                        v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
                        lean_inc(v_a_2612_);
                        lean_dec_ref_known(v___x_2611_, 1);
                        v___x_2613_ = l_Lean_logWarning___at___00Lean_Meta_Simp_checkLoops_spec__1(
                            v_a_2612_,
                            v___y_2591_,
                            v___y_2592_,
                            v___y_2593_,
                            v___y_2594_,
                            v___y_2595_,
                            v___y_2596_,
                            v___y_2597_,
                        );
                        lean_dec(v___y_2591_);
                        return v___x_2613_;
                    } else {
                        lean_dec(v___y_2591_);
                        v_a_2614_ = lean_ctor_get(v___x_2611_, 0);
                        v_isSharedCheck_2621_ = (!lean_is_exclusive(v___x_2611_)) as u8;
                        if v_isSharedCheck_2621_ == 0 {
                            v___x_2616_ = v___x_2611_;
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2614_);
                            lean_dec(v___x_2611_);
                            v___x_2616_ = lean_box(0);
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2606_ == 0 {
                    v___x_2608_ = v___x_2605_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
                    v___x_2608_ = v_reuseFailAlloc_2609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2608_;
            }
            4 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2620_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2619_;
            }
            6 => {
                v___x_2626_ = lean_box(0);
                if v_isShared_2625_ == 0 {
                    lean_ctor_set(v___x_2624_, 0, v___x_2626_);
                    v___x_2628_ = v___x_2624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
                    v___x_2628_ = v_reuseFailAlloc_2629_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2628_;
            }
            8 => {
                v___x_2636_ = l_Lean_Exception_isInterrupt(v_a_2632_);
                if v___x_2636_ == 0 {
                    lean_del_object(v___x_2634_);
                    v_options_2637_ = lean_ctor_get(v___y_2587_, 2);
                    v_hasTrace_2638_ = lean_ctor_get_uint8(
                        v_options_2637_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2638_ == 0 {
                        lean_dec(v_a_2632_);
                        lean_dec_ref(v_origin_2581_);
                        v___y_2591_ = v___y_2582_;
                        v___y_2592_ = v___y_2583_;
                        v___y_2593_ = v___y_2584_;
                        v___y_2594_ = v___y_2585_;
                        v___y_2595_ = v___y_2586_;
                        v___y_2596_ = v___y_2587_;
                        v___y_2597_ = v___y_2588_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2639_ = lean_ctor_get(v___y_2587_, 13);
                        v___x_2640_ = l_Lean_Meta_Simp_checkLoops___lam__0___closed__2;
                        v___x_2641_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_checkLoops___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_checkLoops___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__4,
                        );
                        v___x_2642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2639_,
                            v_options_2637_,
                            v___x_2641_,
                        );
                        if v___x_2642_ == 0 {
                            lean_dec(v_a_2632_);
                            lean_dec_ref(v_origin_2581_);
                            v___y_2591_ = v___y_2582_;
                            v___y_2592_ = v___y_2583_;
                            v___y_2593_ = v___y_2584_;
                            v___y_2594_ = v___y_2585_;
                            v___y_2595_ = v___y_2586_;
                            v___y_2596_ = v___y_2587_;
                            v___y_2597_ = v___y_2588_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2643_ = l_Lean_Meta_ppOrigin___at___00Lean_Meta_Simp_mkLoopWarningMsg_spec__0___redArg(v_origin_2581_);
                            v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
                            lean_inc(v_a_2644_);
                            lean_dec_ref(v___x_2643_);
                            v___x_2645_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__6
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__6_once
                                ),
                                _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__6,
                            );
                            v___x_2646_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                            lean_ctor_set(v___x_2646_, 1, v_a_2644_);
                            v___x_2647_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Simp_checkLoops___lam__0___closed__8_once
                                ),
                                _init_l_Lean_Meta_Simp_checkLoops___lam__0___closed__8,
                            );
                            v___x_2648_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2648_, 0, v___x_2646_);
                            lean_ctor_set(v___x_2648_, 1, v___x_2647_);
                            v___x_2649_ = l_Lean_Exception_toMessageData(v_a_2632_);
                            v___x_2650_ = l_Lean_indentD(v___x_2649_);
                            v___x_2651_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2651_, 0, v___x_2648_);
                            lean_ctor_set(v___x_2651_, 1, v___x_2650_);
                            v___x_2652_ =
                                l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
                                    v___x_2640_,
                                    v___x_2651_,
                                    v___y_2585_,
                                    v___y_2586_,
                                    v___y_2587_,
                                    v___y_2588_,
                                );
                            if lean_obj_tag(v___x_2652_) == 0 {
                                lean_dec_ref_known(v___x_2652_, 1);
                                v___y_2591_ = v___y_2582_;
                                v___y_2592_ = v___y_2583_;
                                v___y_2593_ = v___y_2584_;
                                v___y_2594_ = v___y_2585_;
                                v___y_2595_ = v___y_2586_;
                                v___y_2596_ = v___y_2587_;
                                v___y_2597_ = v___y_2588_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___y_2582_);
                                lean_dec_ref(v_thm_2580_);
                                return v___x_2652_;
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_2582_);
                    lean_dec_ref(v_origin_2581_);
                    lean_dec_ref(v_thm_2580_);
                    if v_isShared_2635_ == 0 {
                        v___x_2654_ = v___x_2634_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2632_);
                        v___x_2654_ = v_reuseFailAlloc_2655_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__0___boxed(
    mut v___x_2657_: *mut LeanObject,
    mut v_force_2658_: *mut LeanObject,
    mut v_thm_2659_: *mut LeanObject,
    mut v_origin_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_force_boxed_2669_: u8 = 0;
    let mut v_res_2670_: *mut LeanObject = core::ptr::null_mut();
    v_force_boxed_2669_ = (lean_unbox(v_force_2658_) as u8);
    v_res_2670_ = l_Lean_Meta_Simp_checkLoops___lam__0(
        v___x_2657_,
        v_force_boxed_2669_,
        v_thm_2659_,
        v_origin_2660_,
        v___y_2661_,
        v___y_2662_,
        v___y_2663_,
        v___y_2664_,
        v___y_2665_,
        v___y_2666_,
        v___y_2667_,
    );
    lean_dec(v___y_2667_);
    lean_dec_ref(v___y_2666_);
    lean_dec(v___y_2665_);
    lean_dec_ref(v___y_2664_);
    lean_dec(v___y_2663_);
    lean_dec_ref(v___y_2662_);
    return v_res_2670_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = lean_box(0);
    v___x_2672_ = lean_unsigned_to_nat(16);
    v___x_2673_ = lean_mk_array(v___x_2672_, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    v___x_2674_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__0_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__0,
    );
    v___x_2675_ = lean_unsigned_to_nat(0);
    v___x_2676_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2676_, 0, v___x_2675_);
    lean_ctor_set(v___x_2676_, 1, v___x_2674_);
    return v___x_2676_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2() -> *mut LeanObject {
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2677_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    v___x_2678_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__2_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__2,
    );
    v___x_2679_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2679_, 0, v___x_2678_);
    return v___x_2679_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2680_ = lean_unsigned_to_nat(0);
    v___x_2681_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
    );
    v___x_2682_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2682_, 0, v___x_2681_);
    lean_ctor_set(v___x_2682_, 1, v___x_2680_);
    return v___x_2682_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5() -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = lean_unsigned_to_nat(32);
    v___x_2684_ = lean_mk_empty_array_with_capacity(v___x_2683_);
    v___x_2685_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2685_, 0, v___x_2684_);
    return v___x_2685_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6() -> *mut LeanObject {
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    v___x_2686_ = 5usize;
    v___x_2687_ = lean_unsigned_to_nat(0);
    v___x_2688_ = lean_unsigned_to_nat(32);
    v___x_2689_ = lean_mk_empty_array_with_capacity(v___x_2688_);
    v___x_2690_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__5_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__5,
    );
    v___x_2691_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2691_, 0, v___x_2690_);
    lean_ctor_set(v___x_2691_, 1, v___x_2689_);
    lean_ctor_set(v___x_2691_, 2, v___x_2687_);
    lean_ctor_set(v___x_2691_, 3, v___x_2687_);
    lean_ctor_set_usize(v___x_2691_, 4, v___x_2686_);
    return v___x_2691_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7() -> *mut LeanObject {
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2692_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__6_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__6,
    );
    v___x_2693_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once),
        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
    );
    v___x_2694_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2694_, 0, v___x_2693_);
    lean_ctor_set(v___x_2694_, 1, v___x_2693_);
    lean_ctor_set(v___x_2694_, 2, v___x_2693_);
    lean_ctor_set(v___x_2694_, 3, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__1(
    mut v_force_2695_: u8,
    mut v_thm_2696_: *mut LeanObject,
    mut v_origin_2697_: *mut LeanObject,
    mut v_a_2698_: u8,
    mut v_ctxt_2699_: *mut LeanObject,
    mut v_methods_2700_: *mut LeanObject,
    mut v___xs_2701_: *mut LeanObject,
    mut v_type_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_unused_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_a_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2706_);
                lean_inc_ref(v___y_2705_);
                lean_inc(v___y_2704_);
                lean_inc_ref(v___y_2703_);
                v___x_2708_ = lean_whnf(
                    v_type_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                    v___y_2706_,
                );
                if lean_obj_tag(v___x_2708_) == 0 {
                    v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
                    lean_inc(v_a_2709_);
                    lean_dec_ref_known(v___x_2708_, 1);
                    v___x_2710_ = l_Lean_Expr_appArg_x21(v_a_2709_);
                    lean_dec(v_a_2709_);
                    v___x_2711_ = lean_box((v_force_2695_) as usize);
                    v___f_2712_ = lean_alloc_closure(
                        l_Lean_Meta_Simp_checkLoops___lam__0___boxed as *mut core::ffi::c_void,
                        12,
                        4,
                    );
                    lean_closure_set(v___f_2712_, 0, v___x_2710_);
                    lean_closure_set(v___f_2712_, 1, v___x_2711_);
                    lean_closure_set(v___f_2712_, 2, v_thm_2696_);
                    lean_closure_set(v___f_2712_, 3, v_origin_2697_);
                    v___x_2713_ = lean_unsigned_to_nat(0);
                    v___x_2714_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__1,
                    );
                    v___x_2715_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__3,
                    );
                    v___x_2716_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_2716_, 0, v___x_2714_);
                    lean_ctor_set(v___x_2716_, 1, v___x_2715_);
                    lean_ctor_set_uint8(
                        v___x_2716_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_a_2698_,
                    );
                    v___x_2717_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__4,
                    );
                    v___x_2718_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_checkLoops___lam__1___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_checkLoops___lam__1___closed__7_once
                        ),
                        _init_l_Lean_Meta_Simp_checkLoops___lam__1___closed__7,
                    );
                    v___x_2719_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v___x_2719_, 0, v___x_2716_);
                    lean_ctor_set(v___x_2719_, 1, v___x_2714_);
                    lean_ctor_set(v___x_2719_, 2, v___x_2714_);
                    lean_ctor_set(v___x_2719_, 3, v___x_2717_);
                    lean_ctor_set(v___x_2719_, 4, v___x_2713_);
                    lean_ctor_set(v___x_2719_, 5, v___x_2718_);
                    v___x_2720_ = l_Lean_Meta_Simp_SimpM_run___redArg(
                        v_ctxt_2699_,
                        v___x_2719_,
                        v_methods_2700_,
                        v___f_2712_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                        v___y_2706_,
                    );
                    if lean_obj_tag(v___x_2720_) == 0 {
                        v_isSharedCheck_2728_ = (!lean_is_exclusive(v___x_2720_)) as u8;
                        if v_isSharedCheck_2728_ == 0 {
                            v_unused_2729_ = lean_ctor_get(v___x_2720_, 0);
                            lean_dec(v_unused_2729_);
                            v___x_2722_ = v___x_2720_;
                            v_isShared_2723_ = v_isSharedCheck_2728_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2720_);
                            v___x_2722_ = lean_box(0);
                            v_isShared_2723_ = v_isSharedCheck_2728_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2730_ = lean_ctor_get(v___x_2720_, 0);
                        v_isSharedCheck_2737_ = (!lean_is_exclusive(v___x_2720_)) as u8;
                        if v_isSharedCheck_2737_ == 0 {
                            v___x_2732_ = v___x_2720_;
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2730_);
                            lean_dec(v___x_2720_);
                            v___x_2732_ = lean_box(0);
                            v_isShared_2733_ = v_isSharedCheck_2737_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_methods_2700_);
                    lean_dec_ref(v_ctxt_2699_);
                    lean_dec_ref(v_origin_2697_);
                    lean_dec_ref(v_thm_2696_);
                    v_a_2738_ = lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2745_ = (!lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2745_ == 0 {
                        v___x_2740_ = v___x_2708_;
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2738_);
                        lean_dec(v___x_2708_);
                        v___x_2740_ = lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2724_ = lean_box(0);
                if v_isShared_2723_ == 0 {
                    lean_ctor_set(v___x_2722_, 0, v___x_2724_);
                    v___x_2726_ = v___x_2722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2726_;
            }
            3 => {
                if v_isShared_2733_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2735_;
            }
            5 => {
                if v_isShared_2741_ == 0 {
                    v___x_2743_ = v___x_2740_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___lam__1___boxed(
    mut v_force_2746_: *mut LeanObject,
    mut v_thm_2747_: *mut LeanObject,
    mut v_origin_2748_: *mut LeanObject,
    mut v_a_2749_: *mut LeanObject,
    mut v_ctxt_2750_: *mut LeanObject,
    mut v_methods_2751_: *mut LeanObject,
    mut v___xs_2752_: *mut LeanObject,
    mut v_type_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
    mut v___y_2756_: *mut LeanObject,
    mut v___y_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_force_boxed_2759_: u8 = 0;
    let mut v_a_25613__boxed_2760_: u8 = 0;
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_force_boxed_2759_ = (lean_unbox(v_force_2746_) as u8);
    v_a_25613__boxed_2760_ = (lean_unbox(v_a_2749_) as u8);
    v_res_2761_ = l_Lean_Meta_Simp_checkLoops___lam__1(
        v_force_boxed_2759_,
        v_thm_2747_,
        v_origin_2748_,
        v_a_25613__boxed_2760_,
        v_ctxt_2750_,
        v_methods_2751_,
        v___xs_2752_,
        v_type_2753_,
        v___y_2754_,
        v___y_2755_,
        v___y_2756_,
        v___y_2757_,
    );
    lean_dec(v___y_2757_);
    lean_dec_ref(v___y_2756_);
    lean_dec(v___y_2755_);
    lean_dec_ref(v___y_2754_);
    lean_dec_ref(v___xs_2752_);
    return v_res_2761_;
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops(
    mut v_force_2762_: u8,
    mut v_ctxt_2763_: *mut LeanObject,
    mut v_methods_2764_: *mut LeanObject,
    mut v_thm_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_a_2768_: *mut LeanObject,
    mut v_a_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_origin_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2811_: u8 = 0;
    let mut v_a_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2771_ = l_Lean_Meta_Simp_shouldCheckLoops(
                    v_force_2762_,
                    v_ctxt_2763_,
                    v_a_2768_,
                    v_a_2769_,
                );
                if lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2811_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2811_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2811_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2772_);
                        lean_dec(v___x_2771_);
                        v___x_2774_ = lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2811_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_thm_2765_);
                    lean_dec_ref(v_methods_2764_);
                    lean_dec_ref(v_ctxt_2763_);
                    v_a_2812_ = lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2819_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2819_ == 0 {
                        v___x_2814_ = v___x_2771_;
                        v_isShared_2815_ = v_isSharedCheck_2819_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2812_);
                        lean_dec(v___x_2771_);
                        v___x_2814_ = lean_box(0);
                        v_isShared_2815_ = v_isSharedCheck_2819_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2776_ = (lean_unbox(v_a_2772_) as u8);
                if v___x_2776_ == 0 {
                    lean_dec(v_a_2772_);
                    lean_dec_ref(v_thm_2765_);
                    lean_dec_ref(v_methods_2764_);
                    lean_dec_ref(v_ctxt_2763_);
                    v___x_2777_ = lean_box(0);
                    if v_isShared_2775_ == 0 {
                        lean_ctor_set(v___x_2774_, 0, v___x_2777_);
                        v___x_2779_ = v___x_2774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
                        v___x_2779_ = v_reuseFailAlloc_2780_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_proof_2781_ = lean_ctor_get(v_thm_2765_, 2);
                    v_origin_2782_ = lean_ctor_get(v_thm_2765_, 4);
                    lean_inc_ref(v_origin_2782_);
                    v___x_2783_ = l_Lean_Expr_hasFVar(v_proof_2781_);
                    if v___x_2783_ == 0 {
                        lean_del_object(v___x_2774_);
                        lean_inc_ref(v_thm_2765_);
                        v___x_2784_ = l_Lean_Meta_SimpTheorem_getValue(
                            v_thm_2765_,
                            v_a_2766_,
                            v_a_2767_,
                            v_a_2768_,
                            v_a_2769_,
                        );
                        if lean_obj_tag(v___x_2784_) == 0 {
                            v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
                            lean_inc(v_a_2785_);
                            lean_dec_ref_known(v___x_2784_, 1);
                            lean_inc(v_a_2769_);
                            lean_inc_ref(v_a_2768_);
                            lean_inc(v_a_2767_);
                            lean_inc_ref(v_a_2766_);
                            v___x_2786_ = lean_infer_type(
                                v_a_2785_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
                            );
                            if lean_obj_tag(v___x_2786_) == 0 {
                                v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
                                lean_inc(v_a_2787_);
                                lean_dec_ref_known(v___x_2786_, 1);
                                v___x_2788_ = lean_box((v_force_2762_) as usize);
                                v___f_2789_ = lean_alloc_closure(
                                    l_Lean_Meta_Simp_checkLoops___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    6,
                                );
                                lean_closure_set(v___f_2789_, 0, v___x_2788_);
                                lean_closure_set(v___f_2789_, 1, v_thm_2765_);
                                lean_closure_set(v___f_2789_, 2, v_origin_2782_);
                                lean_closure_set(v___f_2789_, 3, v_a_2772_);
                                lean_closure_set(v___f_2789_, 4, v_ctxt_2763_);
                                lean_closure_set(v___f_2789_, 5, v_methods_2764_);
                                v___x_2790_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_Simp_checkLoops_spec__3___redArg(v_a_2787_, v___f_2789_, v___x_2783_, v___x_2783_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
                                return v___x_2790_;
                            } else {
                                lean_dec_ref(v_origin_2782_);
                                lean_dec(v_a_2772_);
                                lean_dec_ref(v_thm_2765_);
                                lean_dec_ref(v_methods_2764_);
                                lean_dec_ref(v_ctxt_2763_);
                                v_a_2791_ = lean_ctor_get(v___x_2786_, 0);
                                v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2786_)) as u8;
                                if v_isSharedCheck_2798_ == 0 {
                                    v___x_2793_ = v___x_2786_;
                                    v_isShared_2794_ = v_isSharedCheck_2798_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2791_);
                                    lean_dec(v___x_2786_);
                                    v___x_2793_ = lean_box(0);
                                    v_isShared_2794_ = v_isSharedCheck_2798_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_origin_2782_);
                            lean_dec(v_a_2772_);
                            lean_dec_ref(v_thm_2765_);
                            lean_dec_ref(v_methods_2764_);
                            lean_dec_ref(v_ctxt_2763_);
                            v_a_2799_ = lean_ctor_get(v___x_2784_, 0);
                            v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2784_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2784_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2799_);
                                lean_dec(v___x_2784_);
                                v___x_2801_ = lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_origin_2782_);
                        lean_dec(v_a_2772_);
                        lean_dec_ref(v_thm_2765_);
                        lean_dec_ref(v_methods_2764_);
                        lean_dec_ref(v_ctxt_2763_);
                        v___x_2807_ = lean_box(0);
                        if v_isShared_2775_ == 0 {
                            lean_ctor_set(v___x_2774_, 0, v___x_2807_);
                            v___x_2809_ = v___x_2774_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
                            v___x_2809_ = v_reuseFailAlloc_2810_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2779_;
            }
            3 => {
                if v_isShared_2794_ == 0 {
                    v___x_2796_ = v___x_2793_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2796_;
            }
            5 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2804_;
            }
            7 => {
                return v___x_2809_;
            }
            8 => {
                if v_isShared_2815_ == 0 {
                    v___x_2817_ = v___x_2814_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
                    v___x_2817_ = v_reuseFailAlloc_2818_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_checkLoops___boxed(
    mut v_force_2820_: *mut LeanObject,
    mut v_ctxt_2821_: *mut LeanObject,
    mut v_methods_2822_: *mut LeanObject,
    mut v_thm_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_a_2826_: *mut LeanObject,
    mut v_a_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_force_boxed_2829_: u8 = 0;
    let mut v_res_2830_: *mut LeanObject = core::ptr::null_mut();
    v_force_boxed_2829_ = (lean_unbox(v_force_2820_) as u8);
    v_res_2830_ = l_Lean_Meta_Simp_checkLoops(
        v_force_boxed_2829_,
        v_ctxt_2821_,
        v_methods_2822_,
        v_thm_2823_,
        v_a_2824_,
        v_a_2825_,
        v_a_2826_,
        v_a_2827_,
    );
    lean_dec(v_a_2827_);
    lean_dec_ref(v_a_2826_);
    lean_dec(v_a_2825_);
    lean_dec_ref(v_a_2824_);
    return v_res_2830_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(
    mut v_cls_2831_: *mut LeanObject,
    mut v_msg_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___redArg(
        v_cls_2831_,
        v_msg_2832_,
        v___y_2836_,
        v___y_2837_,
        v___y_2838_,
        v___y_2839_,
    );
    return v___x_2841_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2___boxed(
    mut v_cls_2842_: *mut LeanObject,
    mut v_msg_2843_: *mut LeanObject,
    mut v___y_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
    mut v___y_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2852_: *mut LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_addTrace___at___00Lean_Meta_Simp_checkLoops_spec__2(
        v_cls_2842_,
        v_msg_2843_,
        v___y_2844_,
        v___y_2845_,
        v___y_2846_,
        v___y_2847_,
        v___y_2848_,
        v___y_2849_,
        v___y_2850_,
    );
    lean_dec(v___y_2850_);
    lean_dec_ref(v___y_2849_);
    lean_dec(v___y_2848_);
    lean_dec_ref(v___y_2847_);
    lean_dec(v___y_2846_);
    lean_dec_ref(v___y_2845_);
    lean_dec(v___y_2844_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(
    mut v_ref_2853_: *mut LeanObject,
    mut v_msgData_2854_: *mut LeanObject,
    mut v_severity_2855_: u8,
    mut v_isSilent_2856_: u8,
    mut v___y_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
    mut v___y_2861_: *mut LeanObject,
    mut v___y_2862_: *mut LeanObject,
    mut v___y_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___redArg(v_ref_2853_, v_msgData_2854_, v_severity_2855_, v_isSilent_2856_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
    return v___x_2865_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2___boxed(
    mut v_ref_2866_: *mut LeanObject,
    mut v_msgData_2867_: *mut LeanObject,
    mut v_severity_2868_: *mut LeanObject,
    mut v_isSilent_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2878_: u8 = 0;
    let mut v_isSilent_boxed_2879_: u8 = 0;
    let mut v_res_2880_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2878_ = (lean_unbox(v_severity_2868_) as u8);
    v_isSilent_boxed_2879_ = (lean_unbox(v_isSilent_2869_) as u8);
    v_res_2880_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Meta_Simp_checkLoops_spec__0_spec__0_spec__2(v_ref_2866_, v_msgData_2867_, v_severity_boxed_2878_, v_isSilent_boxed_2879_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
    lean_dec(v___y_2876_);
    lean_dec_ref(v___y_2875_);
    lean_dec(v___y_2874_);
    lean_dec_ref(v___y_2873_);
    lean_dec(v___y_2872_);
    lean_dec_ref(v___y_2871_);
    lean_dec(v___y_2870_);
    lean_dec(v_ref_2866_);
    return v_res_2880_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_LoopProtection_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_LoopProtection_3636494630____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Simp_linter_loopingSimpArgs = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Simp_linter_loopingSimpArgs);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_LoopProtection(builtin);
}
