// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: Lean.Elab.InfoTree.Types Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Elab::InfoTree::Types::{
    initialize_Lean_Elab_InfoTree_Types, runtime_initialize_Lean_Elab_InfoTree_Types,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::l_Lean_mkMVar;
use crate::r#gen::Lean::Level::l_Lean_Level_format;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findLevelIndex_x3f___boxed, l_Lean_instantiateMVarsCore,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox,
};
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 97, 119, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,17690815861033786058 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 105, 110, 116, 32, 114, 97, 119, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 47, 115, 121, 110, 116, 97, 120, 32, 116, 114, 101, 101, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6394840918917265807 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 104, 111, 119, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,17690815861033786058 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject,5762431455154178503 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 105, 110, 116, 32, 96, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 96, 32, 109, 101, 116, 97, 100, 97, 116, 97, 32, 119, 105, 116, 104, 32, 114, 97, 119, 32, 112, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6394840918917265807 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject,4585076390219115590 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 120, 68, 101, 112, 116, 104, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,17690815861033786058 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject,12229127601734880879 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 109, 97, 120, 105, 109, 117, 109, 32, 96, 83, 121, 110, 116, 97, 120, 96, 32, 100, 101, 112, 116, 104, 32, 102, 111, 114, 32, 114, 97, 119, 32, 112, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6394840918917265807 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject,4199523824530911470 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 97, 119, 79, 110, 69, 114, 114, 111, 114, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject,8512788467487830613 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 102, 97, 108, 108, 98, 97, 99, 107, 32, 116, 111, 32, 39, 114, 97, 119, 39, 32, 112, 114, 105, 110, 116, 101, 114, 32, 119, 104, 101, 110, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 32, 102, 97, 105, 108, 115, 0]};
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value) as *mut LeanObject,16537735520416696136 as *mut LeanObject] };
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject,15945868285237937712 as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_instCoeFormatFormatWithInfos___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeFormatFormatWithInfos___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeFormatFormatWithInfos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeFormatFormatWithInfos___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeFormatFormatWithInfos: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeFormatFormatWithInfos___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_Lean_instInhabitedPPFns_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedPPFns_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instInhabitedPPFns_default___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instInhabitedPPFns_default___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__1_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instInhabitedPPFns_default___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__2_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instInhabitedPPFns_default___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__3_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instInhabitedPPFns_default___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__4_value) as *mut LeanObject;
pub static l_Lean_instInhabitedPPFns_default___closed__5_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedPPFns_default___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedPPFns_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedPPFns: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPPFns_default___closed__5_value) as *mut LeanObject;
pub static l_Lean_formatRawGoal___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [103, 111, 97, 108, 32, 0],
};
static mut l_Lean_formatRawGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_formatRawGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_formatRawGoal___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_formatRawGoal___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_formatRawGoal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_formatRawGoal___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_ppExprWithInfos___closed__0_value: LeanStringObject<95> = LeanStringObject {
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
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114,
        105, 110, 116, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 40, 117, 115, 101,
        32, 39, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 114, 97, 119,
        79, 110, 69, 114, 114, 111, 114, 32, 116, 114, 117, 101, 39, 32, 102, 111, 114, 32, 114,
        97, 119, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 41, 0,
    ],
};
static mut l_Lean_ppExprWithInfos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_ppExprWithInfos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__1_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_ppExprWithInfos___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__3_value: LeanStringObject<36> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 58, 32, 0,
    ],
};
static mut l_Lean_ppExprWithInfos___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__3_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__3_value) as *mut LeanObject],
};
static mut l_Lean_ppExprWithInfos___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__4_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__5_value: LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        46, 32, 70, 97, 108, 108, 105, 110, 103, 32, 98, 97, 99, 107, 32, 116, 111, 32, 114, 97,
        119, 32, 112, 114, 105, 110, 116, 101, 114, 46, 93, 0,
    ],
};
static mut l_Lean_ppExprWithInfos___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__5_value) as *mut LeanObject;
pub static l_Lean_ppExprWithInfos___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_ppExprWithInfos___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppExprWithInfos___closed__6_value) as *mut LeanObject;
pub static l_Lean_ppConstNameWithInfos___closed__0_value: LeanStringObject<93> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 93,
    m_capacity: 93,
    m_length: 92,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114,
        105, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 40, 117, 115, 101, 32, 39,
        115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 114, 97, 119, 79, 110,
        69, 114, 114, 111, 114, 32, 116, 114, 117, 101, 39, 32, 102, 111, 114, 32, 114, 97, 119,
        32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 41, 0,
    ],
};
static mut l_Lean_ppConstNameWithInfos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppConstNameWithInfos___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_ppConstNameWithInfos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__1_value) as *mut LeanObject;
pub static l_Lean_ppConstNameWithInfos___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_ppConstNameWithInfos___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppConstNameWithInfos___closed__3_value: LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 99, 111, 110, 115, 116, 97, 110, 116, 58, 32, 0,
    ],
};
static mut l_Lean_ppConstNameWithInfos___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__3_value) as *mut LeanObject;
pub static l_Lean_ppConstNameWithInfos___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__3_value) as *mut LeanObject],
};
static mut l_Lean_ppConstNameWithInfos___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppConstNameWithInfos___closed__4_value) as *mut LeanObject;
pub static l_Lean_ppTerm___closed__0_value: LeanStringObject<89> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 89,
    m_capacity: 89,
    m_length: 88,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114,
        105, 110, 116, 32, 116, 101, 114, 109, 32, 40, 117, 115, 101, 32, 39, 115, 101, 116, 95,
        111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 114, 97, 119, 79, 110, 69, 114, 114, 111,
        114, 32, 116, 114, 117, 101, 39, 32, 102, 111, 114, 32, 114, 97, 119, 32, 114, 101, 112,
        114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 41, 0,
    ],
};
static mut l_Lean_ppTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppTerm___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppTerm___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppTerm___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_ppTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppTerm___closed__1_value) as *mut LeanObject;
pub static l_Lean_ppTerm___closed__2_value: LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 58, 32, 0,
    ],
};
static mut l_Lean_ppTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppTerm___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppTerm___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppTerm___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_ppTerm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppTerm___closed__3_value) as *mut LeanObject;
pub static l_Lean_ppLevel___closed__0_value: LeanStringObject<90> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 90,
    m_capacity: 90,
    m_length: 89,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114,
        105, 110, 116, 32, 108, 101, 118, 101, 108, 32, 40, 117, 115, 101, 32, 39, 115, 101, 116,
        95, 111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 114, 97, 119, 79, 110, 69, 114, 114,
        111, 114, 32, 116, 114, 117, 101, 39, 32, 102, 111, 114, 32, 114, 97, 119, 32, 114, 101,
        112, 114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 41, 0,
    ],
};
static mut l_Lean_ppLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppLevel___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppLevel___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppLevel___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_ppLevel___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppLevel___closed__1_value) as *mut LeanObject;
pub static l_Lean_ppLevel___closed__2_value: LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 108, 101, 118, 101, 108, 58, 32, 0,
    ],
};
static mut l_Lean_ppLevel___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppLevel___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppLevel___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppLevel___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_ppLevel___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppLevel___closed__3_value) as *mut LeanObject;
pub static l_Lean_ppGoal___closed__0_value: LeanStringObject<89> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 89,
    m_capacity: 89,
    m_length: 88,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114,
        105, 110, 116, 32, 103, 111, 97, 108, 32, 40, 117, 115, 101, 32, 39, 115, 101, 116, 95,
        111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 114, 97, 119, 79, 110, 69, 114, 114, 111,
        114, 32, 116, 114, 117, 101, 39, 32, 102, 111, 114, 32, 114, 97, 119, 32, 114, 101, 112,
        114, 101, 115, 101, 110, 116, 97, 116, 105, 111, 110, 41, 0,
    ],
};
static mut l_Lean_ppGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_ppGoal___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppGoal___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_ppGoal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppGoal___closed__1_value) as *mut LeanObject;
pub static l_Lean_ppGoal___closed__2_value: LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 103, 111, 97, 108, 58, 32, 0,
    ],
};
static mut l_Lean_ppGoal___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppGoal___closed__2_value) as *mut LeanObject;
pub static l_Lean_ppGoal___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_ppGoal___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_ppGoal___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ppGoal___closed__3_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(
    mut v_name_606_: *mut LeanObject,
    mut v_decl_607_: *mut LeanObject,
    mut v_ref_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_619_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut v_unused_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_629_: u8 = 0;
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_610_ = lean_ctor_get(v_decl_607_, 0);
                v_descr_611_ = lean_ctor_get(v_decl_607_, 1);
                v_deprecation_x3f_612_ = lean_ctor_get(v_decl_607_, 2);
                v___x_613_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_614_ = (lean_unbox(v_defValue_610_) as u8);
                lean_ctor_set_uint8(v___x_613_, 0 as u32, v___x_614_);
                lean_inc(v_deprecation_x3f_612_);
                lean_inc_ref(v_descr_611_);
                lean_inc_n(v_name_606_, 2);
                v___x_615_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_615_, 0, v_name_606_);
                lean_ctor_set(v___x_615_, 1, v_ref_608_);
                lean_ctor_set(v___x_615_, 2, v___x_613_);
                lean_ctor_set(v___x_615_, 3, v_descr_611_);
                lean_ctor_set(v___x_615_, 4, v_deprecation_x3f_612_);
                v___x_616_ = lean_register_option(v_name_606_, v___x_615_);
                if lean_obj_tag(v___x_616_) == 0 {
                    v_isSharedCheck_624_ = (!lean_is_exclusive(v___x_616_)) as u8;
                    if v_isSharedCheck_624_ == 0 {
                        v_unused_625_ = lean_ctor_get(v___x_616_, 0);
                        lean_dec(v_unused_625_);
                        v___x_618_ = v___x_616_;
                        v_isShared_619_ = v_isSharedCheck_624_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_616_);
                        v___x_618_ = lean_box(0);
                        v_isShared_619_ = v_isSharedCheck_624_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_606_);
                    v_a_626_ = lean_ctor_get(v___x_616_, 0);
                    v_isSharedCheck_633_ = (!lean_is_exclusive(v___x_616_)) as u8;
                    if v_isSharedCheck_633_ == 0 {
                        v___x_628_ = v___x_616_;
                        v_isShared_629_ = v_isSharedCheck_633_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_626_);
                        lean_dec(v___x_616_);
                        v___x_628_ = lean_box(0);
                        v_isShared_629_ = v_isSharedCheck_633_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_610_);
                v___x_620_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_620_, 0, v_name_606_);
                lean_ctor_set(v___x_620_, 1, v_defValue_610_);
                if v_isShared_619_ == 0 {
                    lean_ctor_set(v___x_618_, 0, v___x_620_);
                    v___x_622_ = v___x_618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
                    v___x_622_ = v_reuseFailAlloc_623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_622_;
            }
            3 => {
                if v_isShared_629_ == 0 {
                    v___x_631_ = v___x_628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
                    v___x_631_ = v_reuseFailAlloc_632_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_634_: *mut LeanObject,
    mut v_decl_635_: *mut LeanObject,
    mut v_ref_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_638_: *mut LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v_name_634_, v_decl_635_, v_ref_636_);
    lean_dec_ref(v_decl_635_);
    return v_res_638_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_;
    v___x_657_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_;
    v___x_658_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_;
    v___x_659_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_656_, v___x_657_, v___x_658_);
    return v___x_659_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(
    mut v_a_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_661_: *mut LeanObject = core::ptr::null_mut();
    v_res_661_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
    return v_res_661_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_;
    v___x_680_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_;
    v___x_681_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_;
    v___x_682_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_679_, v___x_680_, v___x_681_);
    return v___x_682_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(
    mut v_a_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
    return v_res_684_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(
    mut v_name_685_: *mut LeanObject,
    mut v_decl_686_: *mut LeanObject,
    mut v_ref_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_697_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_702_: u8 = 0;
    let mut v_unused_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_707_: u8 = 0;
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_689_ = lean_ctor_get(v_decl_686_, 0);
                v_descr_690_ = lean_ctor_get(v_decl_686_, 1);
                v_deprecation_x3f_691_ = lean_ctor_get(v_decl_686_, 2);
                lean_inc(v_defValue_689_);
                v___x_692_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_692_, 0, v_defValue_689_);
                lean_inc(v_deprecation_x3f_691_);
                lean_inc_ref(v_descr_690_);
                lean_inc_n(v_name_685_, 2);
                v___x_693_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_693_, 0, v_name_685_);
                lean_ctor_set(v___x_693_, 1, v_ref_687_);
                lean_ctor_set(v___x_693_, 2, v___x_692_);
                lean_ctor_set(v___x_693_, 3, v_descr_690_);
                lean_ctor_set(v___x_693_, 4, v_deprecation_x3f_691_);
                v___x_694_ = lean_register_option(v_name_685_, v___x_693_);
                if lean_obj_tag(v___x_694_) == 0 {
                    v_isSharedCheck_702_ = (!lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_702_ == 0 {
                        v_unused_703_ = lean_ctor_get(v___x_694_, 0);
                        lean_dec(v_unused_703_);
                        v___x_696_ = v___x_694_;
                        v_isShared_697_ = v_isSharedCheck_702_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_694_);
                        v___x_696_ = lean_box(0);
                        v_isShared_697_ = v_isSharedCheck_702_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_685_);
                    v_a_704_ = lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_711_ = (!lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_711_ == 0 {
                        v___x_706_ = v___x_694_;
                        v_isShared_707_ = v_isSharedCheck_711_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_704_);
                        lean_dec(v___x_694_);
                        v___x_706_ = lean_box(0);
                        v_isShared_707_ = v_isSharedCheck_711_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_689_);
                v___x_698_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_698_, 0, v_name_685_);
                lean_ctor_set(v___x_698_, 1, v_defValue_689_);
                if v_isShared_697_ == 0 {
                    lean_ctor_set(v___x_696_, 0, v___x_698_);
                    v___x_700_ = v___x_696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
                    v___x_700_ = v_reuseFailAlloc_701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_700_;
            }
            3 => {
                if v_isShared_707_ == 0 {
                    v___x_709_ = v___x_706_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
                    v___x_709_ = v_reuseFailAlloc_710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_712_: *mut LeanObject,
    mut v_decl_713_: *mut LeanObject,
    mut v_ref_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v_name_712_, v_decl_713_, v_ref_714_);
    lean_dec_ref(v_decl_713_);
    return v_res_716_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    v___x_733_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_;
    v___x_734_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_;
    v___x_735_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_;
    v___x_736_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v___x_733_, v___x_734_, v___x_735_);
    return v___x_736_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(
    mut v_a_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_738_: *mut LeanObject = core::ptr::null_mut();
    v_res_738_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
    return v_res_738_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_;
    v___x_755_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_;
    v___x_756_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_;
    v___x_757_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_754_, v___x_755_, v___x_756_);
    return v___x_757_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(
    mut v_a_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_759_: *mut LeanObject = core::ptr::null_mut();
    v_res_759_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
    return v_res_759_;
}
pub unsafe fn l_Lean_instCoeFormatFormatWithInfos___lam__0(
    mut v_fmt_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = lean_box(1);
    v___x_762_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_762_, 0, v_fmt_760_);
    lean_ctor_set(v___x_762_, 1, v___x_761_);
    return v___x_762_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__0(
    mut v_x_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = l_Lean_instInhabitedPPFns_default___lam__0___closed__1;
    v___x_772_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__0___boxed(
    mut v_x_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_776_: *mut LeanObject = core::ptr::null_mut();
    v_res_776_ = l_Lean_instInhabitedPPFns_default___lam__0(v_x_773_, v___y_774_);
    lean_dec_ref(v___y_774_);
    lean_dec_ref(v_x_773_);
    return v_res_776_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__1(
    mut v_x_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_instInhabitedPPFns_default___lam__0___closed__1;
    v___x_781_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_781_, 0, v___x_780_);
    return v___x_781_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__1___boxed(
    mut v_x_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_785_ = l_Lean_instInhabitedPPFns_default___lam__1(v_x_782_, v___y_783_);
    lean_dec(v___y_783_);
    lean_dec_ref(v_x_782_);
    return v_res_785_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__2(
    mut v_x_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    v___x_789_ = l_Lean_instInhabitedPPFns_default___lam__0___closed__1;
    v___x_790_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_790_, 0, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__2___boxed(
    mut v_x_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Lean_instInhabitedPPFns_default___lam__2(v_x_791_, v___y_792_);
    lean_dec(v___y_792_);
    lean_dec_ref(v_x_791_);
    return v_res_794_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__3(
    mut v_x_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_instInhabitedPPFns_default___lam__0___closed__1;
    v___x_799_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_799_, 0, v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__3___boxed(
    mut v_x_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
    mut v___y_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_803_: *mut LeanObject = core::ptr::null_mut();
    v_res_803_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_800_, v___y_801_);
    lean_dec(v___y_801_);
    lean_dec_ref(v_x_800_);
    return v_res_803_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__4(
    mut v_x_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_807_ = l_Lean_instInhabitedPPFns_default___lam__0___closed__1;
    v___x_808_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_808_, 0, v___x_807_);
    return v___x_808_;
}
pub unsafe fn l_Lean_instInhabitedPPFns_default___lam__4___boxed(
    mut v_x_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_809_, v___y_810_);
    lean_dec(v___y_810_);
    lean_dec_ref(v_x_809_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(
    mut v_opts_826_: *mut LeanObject,
    mut v_opt_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v_name_828_ = lean_ctor_get(v_opt_827_, 0);
    v_defValue_829_ = lean_ctor_get(v_opt_827_, 1);
    v_map_830_ = lean_ctor_get(v_opts_826_, 0);
    v___x_831_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_830_,
            v_name_828_,
        );
    if lean_obj_tag(v___x_831_) == 0 {
        lean_inc(v_defValue_829_);
        return v_defValue_829_;
    } else {
        let mut v_val_832_: *mut LeanObject = core::ptr::null_mut();
        v_val_832_ = lean_ctor_get(v___x_831_, 0);
        lean_inc(v_val_832_);
        lean_dec_ref_known(v___x_831_, 1);
        if lean_obj_tag(v_val_832_) == 3 {
            let mut v_v_833_: *mut LeanObject = core::ptr::null_mut();
            v_v_833_ = lean_ctor_get(v_val_832_, 0);
            lean_inc(v_v_833_);
            lean_dec_ref_known(v_val_832_, 1);
            return v_v_833_;
        } else {
            lean_dec(v_val_832_);
            lean_inc(v_defValue_829_);
            return v_defValue_829_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(
    mut v_opts_834_: *mut LeanObject,
    mut v_opt_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_836_: *mut LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_834_, v_opt_835_);
    lean_dec_ref(v_opt_835_);
    lean_dec_ref(v_opts_834_);
    return v_res_836_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
    mut v_opts_837_: *mut LeanObject,
    mut v_opt_838_: *mut LeanObject,
) -> u8 {
    let mut v_name_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v_name_839_ = lean_ctor_get(v_opt_838_, 0);
    v_defValue_840_ = lean_ctor_get(v_opt_838_, 1);
    v_map_841_ = lean_ctor_get(v_opts_837_, 0);
    v___x_842_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_841_,
            v_name_839_,
        );
    if lean_obj_tag(v___x_842_) == 0 {
        let mut v___x_843_: u8 = 0;
        v___x_843_ = (lean_unbox(v_defValue_840_) as u8);
        return v___x_843_;
    } else {
        let mut v_val_844_: *mut LeanObject = core::ptr::null_mut();
        v_val_844_ = lean_ctor_get(v___x_842_, 0);
        lean_inc(v_val_844_);
        lean_dec_ref_known(v___x_842_, 1);
        if lean_obj_tag(v_val_844_) == 1 {
            let mut v_v_845_: u8 = 0;
            v_v_845_ = lean_ctor_get_uint8(v_val_844_, 0 as u32);
            lean_dec_ref_known(v_val_844_, 0);
            return v_v_845_;
        } else {
            let mut v___x_846_: u8 = 0;
            lean_dec(v_val_844_);
            v___x_846_ = (lean_unbox(v_defValue_840_) as u8);
            return v___x_846_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(
    mut v_opts_847_: *mut LeanObject,
    mut v_opt_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_849_: u8 = 0;
    let mut v_r_850_: *mut LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_847_, v_opt_848_);
    lean_dec_ref(v_opt_848_);
    lean_dec_ref(v_opts_847_);
    v_r_850_ = lean_box((v_res_849_) as usize);
    return v_r_850_;
}
pub unsafe fn l_Lean_formatRawTerm(
    mut v_ctx_851_: *mut LeanObject,
    mut v_stx_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_opts_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v_opts_853_ = lean_ctor_get(v_ctx_851_, 3);
    v___x_854_ = l_Lean_pp_raw_maxDepth;
    v___x_855_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_853_, v___x_854_);
    v___x_856_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_856_, 0, v___x_855_);
    v___x_857_ = l_Lean_pp_raw_showInfo;
    v___x_858_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_853_, v___x_857_);
    v___x_859_ = l_Lean_Syntax_formatStx(v_stx_852_, v___x_856_, v___x_858_);
    return v___x_859_;
}
pub unsafe fn l_Lean_formatRawTerm___boxed(
    mut v_ctx_860_: *mut LeanObject,
    mut v_stx_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_862_: *mut LeanObject = core::ptr::null_mut();
    v_res_862_ = l_Lean_formatRawTerm(v_ctx_860_, v_stx_861_);
    lean_dec_ref(v_ctx_860_);
    return v_res_862_;
}
pub unsafe fn l_Lean_formatRawGoal(mut v_mvarId_866_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Lean_formatRawGoal___closed__1;
    v___x_868_ = l_Lean_mkMVar(v_mvarId_866_);
    v___x_869_ = lean_expr_dbg_to_string(v___x_868_);
    lean_dec_ref(v___x_868_);
    v___x_870_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_870_, 0, v___x_869_);
    v___x_871_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_871_, 0, v___x_867_);
    lean_ctor_set(v___x_871_, 1, v___x_870_);
    return v___x_871_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(
    mut v_x_872_: *mut LeanObject,
    mut v_e_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = lean_expr_dbg_to_string(v_e_873_);
    v___x_876_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_876_, 0, v___x_875_);
    v___x_877_ = lean_box(1);
    v___x_878_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_878_, 0, v___x_876_);
    lean_ctor_set(v___x_878_, 1, v___x_877_);
    v___x_879_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_879_, 0, v___x_878_);
    return v___x_879_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_x_880_: *mut LeanObject,
    mut v_e_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_880_, v_e_881_);
    lean_dec_ref(v_e_881_);
    lean_dec_ref(v_x_880_);
    return v_res_883_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(
    mut v_x_884_: *mut LeanObject,
    mut v_n_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_887_: u8 = 0;
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    v___x_887_ = 1;
    v___x_888_ = l_Lean_Name_toString(v_n_885_, v___x_887_);
    v___x_889_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_889_, 0, v___x_888_);
    v___x_890_ = lean_box(1);
    v___x_891_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_891_, 0, v___x_889_);
    lean_ctor_set(v___x_891_, 1, v___x_890_);
    v___x_892_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_892_, 0, v___x_891_);
    return v___x_892_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_x_893_: *mut LeanObject,
    mut v_n_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_896_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_893_, v_n_894_);
    lean_dec_ref(v_x_893_);
    return v_res_896_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(
    mut v_ctx_897_: *mut LeanObject,
    mut v_stx_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_formatRawTerm(v_ctx_897_, v_stx_898_);
    v___x_901_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_901_, 0, v___x_900_);
    return v___x_901_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_ctx_902_: *mut LeanObject,
    mut v_stx_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_902_, v_stx_903_);
    lean_dec_ref(v_ctx_902_);
    return v_res_905_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(
    mut v_ctx_906_: *mut LeanObject,
    mut v_l_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mctx_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v_mctx_909_ = lean_ctor_get(v_ctx_906_, 1);
    lean_inc_ref(v_mctx_909_);
    lean_dec_ref(v_ctx_906_);
    v___x_910_ = 1;
    v___x_911_ = lean_alloc_closure(
        l_Lean_MetavarContext_findLevelIndex_x3f___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_911_, 0, v_mctx_909_);
    v___x_912_ = l_Lean_Level_format(v_l_907_, v___x_910_, v___x_911_);
    v___x_913_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_913_, 0, v___x_912_);
    return v___x_913_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_ctx_914_: *mut LeanObject,
    mut v_l_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_917_: *mut LeanObject = core::ptr::null_mut();
    v_res_917_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_914_, v_l_915_);
    return v_res_917_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(
    mut v_x_918_: *mut LeanObject,
    mut v_mvarId_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___x_921_ = l_Lean_formatRawGoal(v_mvarId_919_);
    v___x_922_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_922_, 0, v___x_921_);
    return v___x_922_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_x_923_: *mut LeanObject,
    mut v_mvarId_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_926_: *mut LeanObject = core::ptr::null_mut();
    v_res_926_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_923_, v_mvarId_924_);
    lean_dec_ref(v_x_923_);
    return v_res_926_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    v___x_939_ = l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_;
    v___x_940_ = lean_st_mk_ref(v___x_939_);
    v___x_941_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_941_, 0, v___x_940_);
    return v___x_941_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(
    mut v_a_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_943_: *mut LeanObject = core::ptr::null_mut();
    v_res_943_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
    return v_res_943_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(
    mut v___x_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    v___x_946_ = lean_st_ref_get(v___x_944_);
    v___x_947_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_947_, 0, v___x_946_);
    return v___x_947_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(
    mut v___x_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_res_950_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_948_);
    lean_dec(v___x_948_);
    return v_res_950_;
}
pub unsafe fn _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_952_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Lean_ppFnsRef;
    v___f_952_ = lean_alloc_closure(l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_952_, 0, v___x_951_);
    return v___f_952_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___f_954_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once), _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
    v___x_955_ = lean_box(0);
    v___x_956_ = lean_box(2);
    v___x_957_ = l_Lean_registerEnvExtension___redArg(v___f_954_, v___x_955_, v___x_956_);
    return v___x_957_;
}
pub unsafe fn l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(
    mut v_a_958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_959_: *mut LeanObject = core::ptr::null_mut();
    v_res_959_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
    return v_res_959_;
}
pub unsafe fn l_Lean_ppExprWithInfos(
    mut v_ctx_972_: *mut LeanObject,
    mut v_e_973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ppExprWithInfos_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: u8 = 0;
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1022_: u8 = 0;
    let mut v_unused_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_975_ = lean_ctor_get(v_ctx_972_, 0);
                v_mctx_976_ = lean_ctor_get(v_ctx_972_, 1);
                v_opts_977_ = lean_ctor_get(v_ctx_972_, 3);
                lean_inc_ref(v_opts_977_);
                v___x_978_ = l_Lean_pp_raw;
                v___x_979_ =
                    l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_977_, v___x_978_);
                if v___x_979_ == 0 {
                    v___x_980_ = l_Lean_ppExt;
                    v_asyncMode_981_ = lean_ctor_get(v___x_980_, 2);
                    v___x_982_ = l_Lean_instInhabitedPPFns_default;
                    v___x_983_ = lean_box(0);
                    lean_inc_ref(v_env_975_);
                    v___x_984_ =
                        l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                            v___x_982_,
                            v___x_980_,
                            v_env_975_,
                            v_asyncMode_981_,
                            v___x_983_,
                        );
                    v_ppExprWithInfos_985_ = lean_ctor_get(v___x_984_, 0);
                    lean_inc_ref(v_ppExprWithInfos_985_);
                    lean_dec(v___x_984_);
                    lean_inc_ref(v_e_973_);
                    v___x_986_ =
                        lean_apply_3(v_ppExprWithInfos_985_, v_ctx_972_, v_e_973_, lean_box(0));
                    if lean_obj_tag(v___x_986_) == 0 {
                        lean_dec_ref(v_opts_977_);
                        lean_dec_ref(v_e_973_);
                        v_a_987_ = lean_ctor_get(v___x_986_, 0);
                        lean_inc(v_a_987_);
                        lean_dec_ref_known(v___x_986_, 1);
                        return v_a_987_;
                    } else {
                        v_a_988_ = lean_ctor_get(v___x_986_, 0);
                        v_isSharedCheck_1010_ = (!lean_is_exclusive(v___x_986_)) as u8;
                        if v_isSharedCheck_1010_ == 0 {
                            v___x_990_ = v___x_986_;
                            v_isShared_991_ = v_isSharedCheck_1010_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_988_);
                            lean_dec(v___x_986_);
                            v___x_990_ = lean_box(0);
                            v_isShared_991_ = v_isSharedCheck_1010_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_mctx_976_);
                    lean_dec_ref(v_opts_977_);
                    lean_dec_ref(v_ctx_972_);
                    v___x_1011_ = l_Lean_instantiateMVarsCore(v_mctx_976_, v_e_973_);
                    v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
                    v_isSharedCheck_1022_ = (!lean_is_exclusive(v___x_1011_)) as u8;
                    if v_isSharedCheck_1022_ == 0 {
                        v_unused_1023_ = lean_ctor_get(v___x_1011_, 1);
                        lean_dec(v_unused_1023_);
                        v___x_1014_ = v___x_1011_;
                        v_isShared_1015_ = v_isSharedCheck_1022_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_fst_1012_);
                        lean_dec(v___x_1011_);
                        v___x_1014_ = lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1022_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_992_ = l_Lean_pp_rawOnError;
                v___x_993_ =
                    l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_977_, v___x_992_);
                lean_dec_ref(v_opts_977_);
                if v___x_993_ == 0 {
                    lean_del_object(v___x_990_);
                    lean_dec(v_a_988_);
                    lean_dec_ref(v_e_973_);
                    v___x_994_ = l_Lean_ppExprWithInfos___closed__2;
                    return v___x_994_;
                } else {
                    v___x_995_ = l_Lean_ppExprWithInfos___closed__4;
                    v___x_996_ = lean_io_error_to_string(v_a_988_);
                    if v_isShared_991_ == 0 {
                        lean_ctor_set_tag(v___x_990_, 3);
                        lean_ctor_set(v___x_990_, 0, v___x_996_);
                        v___x_998_ = v___x_990_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1009_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_996_);
                        v___x_998_ = v_reuseFailAlloc_1009_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_999_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_999_, 0, v___x_995_);
                lean_ctor_set(v___x_999_, 1, v___x_998_);
                v___x_1000_ = l_Lean_ppExprWithInfos___closed__6;
                v___x_1001_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1001_, 0, v___x_999_);
                lean_ctor_set(v___x_1001_, 1, v___x_1000_);
                v___x_1002_ = lean_box(1);
                v___x_1003_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1003_, 0, v___x_1001_);
                lean_ctor_set(v___x_1003_, 1, v___x_1002_);
                v___x_1004_ = lean_expr_dbg_to_string(v_e_973_);
                lean_dec_ref(v_e_973_);
                v___x_1005_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1005_, 0, v___x_1004_);
                v___x_1006_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1006_, 0, v___x_1003_);
                lean_ctor_set(v___x_1006_, 1, v___x_1005_);
                v___x_1007_ = lean_box(1);
                v___x_1008_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1008_, 0, v___x_1006_);
                lean_ctor_set(v___x_1008_, 1, v___x_1007_);
                return v___x_1008_;
            }
            3 => {
                v___x_1016_ = lean_expr_dbg_to_string(v_fst_1012_);
                lean_dec(v_fst_1012_);
                v___x_1017_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1017_, 0, v___x_1016_);
                v___x_1018_ = lean_box(1);
                if v_isShared_1015_ == 0 {
                    lean_ctor_set(v___x_1014_, 1, v___x_1018_);
                    lean_ctor_set(v___x_1014_, 0, v___x_1017_);
                    v___x_1020_ = v___x_1014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1017_);
                    lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1018_);
                    v___x_1020_ = v_reuseFailAlloc_1021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppExprWithInfos___boxed(
    mut v_ctx_1024_: *mut LeanObject,
    mut v_e_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1027_: *mut LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Lean_ppExprWithInfos(v_ctx_1024_, v_e_1025_);
    return v_res_1027_;
}
pub unsafe fn l_Lean_ppConstNameWithInfos(
    mut v_ctx_1037_: *mut LeanObject,
    mut v_n_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ppConstNameWithInfos_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_1040_ = lean_ctor_get(v_ctx_1037_, 0);
                v_opts_1041_ = lean_ctor_get(v_ctx_1037_, 3);
                lean_inc_ref(v_opts_1041_);
                v___x_1042_ = l_Lean_ppExt;
                v_asyncMode_1043_ = lean_ctor_get(v___x_1042_, 2);
                v___x_1044_ = l_Lean_instInhabitedPPFns_default;
                v___x_1045_ = lean_box(0);
                lean_inc_ref(v_env_1040_);
                v___x_1046_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1044_,
                        v___x_1042_,
                        v_env_1040_,
                        v_asyncMode_1043_,
                        v___x_1045_,
                    );
                v_ppConstNameWithInfos_1047_ = lean_ctor_get(v___x_1046_, 1);
                lean_inc_ref(v_ppConstNameWithInfos_1047_);
                lean_dec(v___x_1046_);
                lean_inc(v_n_1038_);
                v___x_1048_ = lean_apply_3(
                    v_ppConstNameWithInfos_1047_,
                    v_ctx_1037_,
                    v_n_1038_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1048_) == 0 {
                    lean_dec_ref(v_opts_1041_);
                    lean_dec(v_n_1038_);
                    v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
                    lean_inc(v_a_1049_);
                    lean_dec_ref_known(v___x_1048_, 1);
                    return v_a_1049_;
                } else {
                    v_a_1050_ = lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1072_ = (!lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1072_ == 0 {
                        v___x_1052_ = v___x_1048_;
                        v_isShared_1053_ = v_isSharedCheck_1072_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1050_);
                        lean_dec(v___x_1048_);
                        v___x_1052_ = lean_box(0);
                        v_isShared_1053_ = v_isSharedCheck_1072_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1054_ = l_Lean_pp_rawOnError;
                v___x_1055_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
                    v_opts_1041_,
                    v___x_1054_,
                );
                lean_dec_ref(v_opts_1041_);
                if v___x_1055_ == 0 {
                    lean_del_object(v___x_1052_);
                    lean_dec(v_a_1050_);
                    lean_dec(v_n_1038_);
                    v___x_1056_ = l_Lean_ppConstNameWithInfos___closed__2;
                    return v___x_1056_;
                } else {
                    v___x_1057_ = l_Lean_ppConstNameWithInfos___closed__4;
                    v___x_1058_ = lean_io_error_to_string(v_a_1050_);
                    if v_isShared_1053_ == 0 {
                        lean_ctor_set_tag(v___x_1052_, 3);
                        lean_ctor_set(v___x_1052_, 0, v___x_1058_);
                        v___x_1060_ = v___x_1052_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1071_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1058_);
                        v___x_1060_ = v_reuseFailAlloc_1071_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1061_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1061_, 0, v___x_1057_);
                lean_ctor_set(v___x_1061_, 1, v___x_1060_);
                v___x_1062_ = l_Lean_ppExprWithInfos___closed__6;
                v___x_1063_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1063_, 0, v___x_1061_);
                lean_ctor_set(v___x_1063_, 1, v___x_1062_);
                v___x_1064_ = lean_box(1);
                v___x_1065_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1065_, 0, v___x_1063_);
                lean_ctor_set(v___x_1065_, 1, v___x_1064_);
                v___x_1066_ = l_Lean_Name_toString(v_n_1038_, v___x_1055_);
                v___x_1067_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1067_, 0, v___x_1066_);
                v___x_1068_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1068_, 0, v___x_1065_);
                lean_ctor_set(v___x_1068_, 1, v___x_1067_);
                v___x_1069_ = lean_box(1);
                v___x_1070_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1070_, 0, v___x_1068_);
                lean_ctor_set(v___x_1070_, 1, v___x_1069_);
                return v___x_1070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppConstNameWithInfos___boxed(
    mut v_ctx_1073_: *mut LeanObject,
    mut v_n_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1076_: *mut LeanObject = core::ptr::null_mut();
    v_res_1076_ = l_Lean_ppConstNameWithInfos(v_ctx_1073_, v_n_1074_);
    return v_res_1076_;
}
pub unsafe fn l_Lean_ppTerm(
    mut v_ctx_1083_: *mut LeanObject,
    mut v_stx_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ppTerm_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_1086_ = lean_ctor_get(v_ctx_1083_, 0);
                v_opts_1087_ = lean_ctor_get(v_ctx_1083_, 3);
                v___x_1088_ = l_Lean_pp_raw;
                v___x_1089_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
                    v_opts_1087_,
                    v___x_1088_,
                );
                if v___x_1089_ == 0 {
                    v___x_1090_ = l_Lean_ppExt;
                    v_asyncMode_1091_ = lean_ctor_get(v___x_1090_, 2);
                    v___x_1092_ = l_Lean_instInhabitedPPFns_default;
                    v___x_1093_ = lean_box(0);
                    lean_inc_ref(v_env_1086_);
                    v___x_1094_ =
                        l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                            v___x_1092_,
                            v___x_1090_,
                            v_env_1086_,
                            v_asyncMode_1091_,
                            v___x_1093_,
                        );
                    v_ppTerm_1095_ = lean_ctor_get(v___x_1094_, 2);
                    lean_inc_ref(v_ppTerm_1095_);
                    lean_dec(v___x_1094_);
                    lean_inc(v_stx_1084_);
                    lean_inc_ref(v_ctx_1083_);
                    v___x_1096_ =
                        lean_apply_3(v_ppTerm_1095_, v_ctx_1083_, v_stx_1084_, lean_box(0));
                    if lean_obj_tag(v___x_1096_) == 0 {
                        lean_dec(v_stx_1084_);
                        lean_dec_ref(v_ctx_1083_);
                        v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
                        lean_inc(v_a_1097_);
                        lean_dec_ref_known(v___x_1096_, 1);
                        return v_a_1097_;
                    } else {
                        v_a_1098_ = lean_ctor_get(v___x_1096_, 0);
                        v_isSharedCheck_1117_ = (!lean_is_exclusive(v___x_1096_)) as u8;
                        if v_isSharedCheck_1117_ == 0 {
                            v___x_1100_ = v___x_1096_;
                            v_isShared_1101_ = v_isSharedCheck_1117_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1098_);
                            lean_dec(v___x_1096_);
                            v___x_1100_ = lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1117_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1118_ = l_Lean_formatRawTerm(v_ctx_1083_, v_stx_1084_);
                    lean_dec_ref(v_ctx_1083_);
                    return v___x_1118_;
                }
            }
            1 => {
                v___x_1102_ = l_Lean_pp_rawOnError;
                v___x_1103_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
                    v_opts_1087_,
                    v___x_1102_,
                );
                if v___x_1103_ == 0 {
                    lean_del_object(v___x_1100_);
                    lean_dec(v_a_1098_);
                    lean_dec(v_stx_1084_);
                    lean_dec_ref(v_ctx_1083_);
                    v___x_1104_ = l_Lean_ppTerm___closed__1;
                    return v___x_1104_;
                } else {
                    v___x_1105_ = l_Lean_ppTerm___closed__3;
                    v___x_1106_ = lean_io_error_to_string(v_a_1098_);
                    if v_isShared_1101_ == 0 {
                        lean_ctor_set_tag(v___x_1100_, 3);
                        lean_ctor_set(v___x_1100_, 0, v___x_1106_);
                        v___x_1108_ = v___x_1100_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1116_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1106_);
                        v___x_1108_ = v_reuseFailAlloc_1116_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1109_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1109_, 0, v___x_1105_);
                lean_ctor_set(v___x_1109_, 1, v___x_1108_);
                v___x_1110_ = l_Lean_ppExprWithInfos___closed__6;
                v___x_1111_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1111_, 0, v___x_1109_);
                lean_ctor_set(v___x_1111_, 1, v___x_1110_);
                v___x_1112_ = lean_box(1);
                v___x_1113_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1113_, 0, v___x_1111_);
                lean_ctor_set(v___x_1113_, 1, v___x_1112_);
                v___x_1114_ = l_Lean_formatRawTerm(v_ctx_1083_, v_stx_1084_);
                lean_dec_ref(v_ctx_1083_);
                v___x_1115_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1115_, 0, v___x_1113_);
                lean_ctor_set(v___x_1115_, 1, v___x_1114_);
                return v___x_1115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppTerm___boxed(
    mut v_ctx_1119_: *mut LeanObject,
    mut v_stx_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Lean_ppTerm(v_ctx_1119_, v_stx_1120_);
    return v_res_1122_;
}
pub unsafe fn l_Lean_ppLevel(
    mut v_ctx_1129_: *mut LeanObject,
    mut v_l_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ppLevel_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_1132_ = lean_ctor_get(v_ctx_1129_, 0);
                v_mctx_1133_ = lean_ctor_get(v_ctx_1129_, 1);
                lean_inc_ref(v_mctx_1133_);
                v_opts_1134_ = lean_ctor_get(v_ctx_1129_, 3);
                lean_inc_ref(v_opts_1134_);
                v___x_1135_ = l_Lean_ppExt;
                v_asyncMode_1136_ = lean_ctor_get(v___x_1135_, 2);
                v___x_1137_ = l_Lean_instInhabitedPPFns_default;
                v___x_1138_ = lean_box(0);
                lean_inc_ref(v_env_1132_);
                v___x_1139_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1137_,
                        v___x_1135_,
                        v_env_1132_,
                        v_asyncMode_1136_,
                        v___x_1138_,
                    );
                v_ppLevel_1140_ = lean_ctor_get(v___x_1139_, 3);
                lean_inc_ref(v_ppLevel_1140_);
                lean_dec(v___x_1139_);
                lean_inc(v_l_1130_);
                v___x_1141_ = lean_apply_3(v_ppLevel_1140_, v_ctx_1129_, v_l_1130_, lean_box(0));
                if lean_obj_tag(v___x_1141_) == 0 {
                    lean_dec_ref(v_opts_1134_);
                    lean_dec_ref(v_mctx_1133_);
                    lean_dec(v_l_1130_);
                    v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
                    lean_inc(v_a_1142_);
                    lean_dec_ref_known(v___x_1141_, 1);
                    return v_a_1142_;
                } else {
                    v_a_1143_ = lean_ctor_get(v___x_1141_, 0);
                    v_isSharedCheck_1163_ = (!lean_is_exclusive(v___x_1141_)) as u8;
                    if v_isSharedCheck_1163_ == 0 {
                        v___x_1145_ = v___x_1141_;
                        v_isShared_1146_ = v_isSharedCheck_1163_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1143_);
                        lean_dec(v___x_1141_);
                        v___x_1145_ = lean_box(0);
                        v_isShared_1146_ = v_isSharedCheck_1163_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1147_ = l_Lean_pp_rawOnError;
                v___x_1148_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
                    v_opts_1134_,
                    v___x_1147_,
                );
                lean_dec_ref(v_opts_1134_);
                if v___x_1148_ == 0 {
                    lean_del_object(v___x_1145_);
                    lean_dec(v_a_1143_);
                    lean_dec_ref(v_mctx_1133_);
                    lean_dec(v_l_1130_);
                    v___x_1149_ = l_Lean_ppLevel___closed__1;
                    return v___x_1149_;
                } else {
                    v___x_1150_ = l_Lean_ppLevel___closed__3;
                    v___x_1151_ = lean_io_error_to_string(v_a_1143_);
                    if v_isShared_1146_ == 0 {
                        lean_ctor_set_tag(v___x_1145_, 3);
                        lean_ctor_set(v___x_1145_, 0, v___x_1151_);
                        v___x_1153_ = v___x_1145_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1162_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1151_);
                        v___x_1153_ = v_reuseFailAlloc_1162_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1154_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1154_, 0, v___x_1150_);
                lean_ctor_set(v___x_1154_, 1, v___x_1153_);
                v___x_1155_ = l_Lean_ppExprWithInfos___closed__6;
                v___x_1156_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1156_, 0, v___x_1154_);
                lean_ctor_set(v___x_1156_, 1, v___x_1155_);
                v___x_1157_ = lean_box(1);
                v___x_1158_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1158_, 0, v___x_1156_);
                lean_ctor_set(v___x_1158_, 1, v___x_1157_);
                v___x_1159_ = lean_alloc_closure(
                    l_Lean_MetavarContext_findLevelIndex_x3f___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___x_1159_, 0, v_mctx_1133_);
                v___x_1160_ = l_Lean_Level_format(v_l_1130_, v___x_1148_, v___x_1159_);
                v___x_1161_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1161_, 0, v___x_1158_);
                lean_ctor_set(v___x_1161_, 1, v___x_1160_);
                return v___x_1161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppLevel___boxed(
    mut v_ctx_1164_: *mut LeanObject,
    mut v_l_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v_res_1167_ = l_Lean_ppLevel(v_ctx_1164_, v_l_1165_);
    return v_res_1167_;
}
pub unsafe fn l_Lean_ppGoal(
    mut v_ctx_1174_: *mut LeanObject,
    mut v_mvarId_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ppGoal_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_1177_ = lean_ctor_get(v_ctx_1174_, 0);
                v_opts_1178_ = lean_ctor_get(v_ctx_1174_, 3);
                lean_inc_ref(v_opts_1178_);
                v___x_1179_ = l_Lean_ppExt;
                v_asyncMode_1180_ = lean_ctor_get(v___x_1179_, 2);
                v___x_1181_ = l_Lean_instInhabitedPPFns_default;
                v___x_1182_ = lean_box(0);
                lean_inc_ref(v_env_1177_);
                v___x_1183_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1181_,
                        v___x_1179_,
                        v_env_1177_,
                        v_asyncMode_1180_,
                        v___x_1182_,
                    );
                v_ppGoal_1184_ = lean_ctor_get(v___x_1183_, 4);
                lean_inc_ref(v_ppGoal_1184_);
                lean_dec(v___x_1183_);
                lean_inc(v_mvarId_1175_);
                v___x_1185_ =
                    lean_apply_3(v_ppGoal_1184_, v_ctx_1174_, v_mvarId_1175_, lean_box(0));
                if lean_obj_tag(v___x_1185_) == 0 {
                    lean_dec_ref(v_opts_1178_);
                    lean_dec(v_mvarId_1175_);
                    v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
                    lean_inc(v_a_1186_);
                    lean_dec_ref_known(v___x_1185_, 1);
                    return v_a_1186_;
                } else {
                    v_a_1187_ = lean_ctor_get(v___x_1185_, 0);
                    v_isSharedCheck_1206_ = (!lean_is_exclusive(v___x_1185_)) as u8;
                    if v_isSharedCheck_1206_ == 0 {
                        v___x_1189_ = v___x_1185_;
                        v_isShared_1190_ = v_isSharedCheck_1206_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1187_);
                        lean_dec(v___x_1185_);
                        v___x_1189_ = lean_box(0);
                        v_isShared_1190_ = v_isSharedCheck_1206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1191_ = l_Lean_pp_rawOnError;
                v___x_1192_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(
                    v_opts_1178_,
                    v___x_1191_,
                );
                lean_dec_ref(v_opts_1178_);
                if v___x_1192_ == 0 {
                    lean_del_object(v___x_1189_);
                    lean_dec(v_a_1187_);
                    lean_dec(v_mvarId_1175_);
                    v___x_1193_ = l_Lean_ppGoal___closed__1;
                    return v___x_1193_;
                } else {
                    v___x_1194_ = l_Lean_ppGoal___closed__3;
                    v___x_1195_ = lean_io_error_to_string(v_a_1187_);
                    if v_isShared_1190_ == 0 {
                        lean_ctor_set_tag(v___x_1189_, 3);
                        lean_ctor_set(v___x_1189_, 0, v___x_1195_);
                        v___x_1197_ = v___x_1189_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1205_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1195_);
                        v___x_1197_ = v_reuseFailAlloc_1205_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1198_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1198_, 0, v___x_1194_);
                lean_ctor_set(v___x_1198_, 1, v___x_1197_);
                v___x_1199_ = l_Lean_ppExprWithInfos___closed__6;
                v___x_1200_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1200_, 0, v___x_1198_);
                lean_ctor_set(v___x_1200_, 1, v___x_1199_);
                v___x_1201_ = lean_box(1);
                v___x_1202_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1202_, 0, v___x_1200_);
                lean_ctor_set(v___x_1202_, 1, v___x_1201_);
                v___x_1203_ = l_Lean_formatRawGoal(v_mvarId_1175_);
                v___x_1204_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1204_, 0, v___x_1202_);
                lean_ctor_set(v___x_1204_, 1, v___x_1203_);
                return v___x_1204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ppGoal___boxed(
    mut v_ctx_1207_: *mut LeanObject,
    mut v_mvarId_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1210_: *mut LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_Lean_ppGoal(v_ctx_1207_, v_mvarId_1208_);
    return v_res_1210_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_PPExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_raw = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_raw);
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_raw_showInfo = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_raw_showInfo);
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_raw_maxDepth = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_raw_maxDepth);
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_rawOnError = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_pp_rawOnError);
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ppFnsRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_ppFnsRef);
    lean_dec_ref(res);
    res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ppExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_ppExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_PPExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_PPExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_PPExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_PPExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_PPExt(builtin);
}
