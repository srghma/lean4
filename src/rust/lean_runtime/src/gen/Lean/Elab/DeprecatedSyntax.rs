// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax
// Imports: Lean.MonadEnv Lean.Linter.Init Lean.Elab.Util
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr3, l_Lean_Name_mkStr5, l_Lean_Syntax_getKind};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Elab::Util::{
    initialize_Lean_Elab_Util, runtime_initialize_Lean_Elab_Util,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_logLintIf___redArg,
    runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::MonadEnv::{initialize_Lean_MonadEnv, runtime_initialize_Lean_MonadEnv};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,13546154976408593379 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,1829946577588164054 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 119, 104, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 105, 115, 32, 117, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,14679817356290926072 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,9479425830589914185 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 83, 121, 110, 116, 97, 120, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,16340096650070628312 as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value: LeanStringObject<
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
    m_data: [109, 97, 99, 114, 111, 32, 39, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value: LeanStringObject<
    30,
> = LeanStringObject {
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
        32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 32, 115, 121, 110, 116, 97, 120, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value: LeanStringObject<
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
    m_data: [115, 121, 110, 116, 97, 120, 32, 39, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value: LeanStringObject<
    22,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        39, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 0,
    ],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value:
    LeanStringObject<31> = LeanStringObject {
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
        39, 32, 112, 114, 111, 100, 117, 99, 101, 115, 32, 100, 101, 112, 114, 101, 99, 97, 116,
        101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        32, 40, 101, 120, 112, 97, 110, 100, 101, 100, 32, 102, 114, 111, 109, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [39, 41, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value:
    LeanStringObject<1> = LeanStringObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(
    mut v_name_325_: *mut LeanObject,
    mut v_decl_326_: *mut LeanObject,
    mut v_ref_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_343_: u8 = 0;
    let mut v_unused_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_348_: u8 = 0;
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_329_ = lean_ctor_get(v_decl_326_, 0);
                v_descr_330_ = lean_ctor_get(v_decl_326_, 1);
                v_deprecation_x3f_331_ = lean_ctor_get(v_decl_326_, 2);
                v___x_332_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_333_ = (lean_unbox(v_defValue_329_) as u8);
                lean_ctor_set_uint8(v___x_332_, 0 as u32, v___x_333_);
                lean_inc(v_deprecation_x3f_331_);
                lean_inc_ref(v_descr_330_);
                lean_inc_n(v_name_325_, 2);
                v___x_334_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_334_, 0, v_name_325_);
                lean_ctor_set(v___x_334_, 1, v_ref_327_);
                lean_ctor_set(v___x_334_, 2, v___x_332_);
                lean_ctor_set(v___x_334_, 3, v_descr_330_);
                lean_ctor_set(v___x_334_, 4, v_deprecation_x3f_331_);
                v___x_335_ = lean_register_option(v_name_325_, v___x_334_);
                if lean_obj_tag(v___x_335_) == 0 {
                    v_isSharedCheck_343_ = (!lean_is_exclusive(v___x_335_)) as u8;
                    if v_isSharedCheck_343_ == 0 {
                        v_unused_344_ = lean_ctor_get(v___x_335_, 0);
                        lean_dec(v_unused_344_);
                        v___x_337_ = v___x_335_;
                        v_isShared_338_ = v_isSharedCheck_343_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_335_);
                        v___x_337_ = lean_box(0);
                        v_isShared_338_ = v_isSharedCheck_343_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_325_);
                    v_a_345_ = lean_ctor_get(v___x_335_, 0);
                    v_isSharedCheck_352_ = (!lean_is_exclusive(v___x_335_)) as u8;
                    if v_isSharedCheck_352_ == 0 {
                        v___x_347_ = v___x_335_;
                        v_isShared_348_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_345_);
                        lean_dec(v___x_335_);
                        v___x_347_ = lean_box(0);
                        v_isShared_348_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_329_);
                v___x_339_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_339_, 0, v_name_325_);
                lean_ctor_set(v___x_339_, 1, v_defValue_329_);
                if v_isShared_338_ == 0 {
                    lean_ctor_set(v___x_337_, 0, v___x_339_);
                    v___x_341_ = v___x_337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
                    v___x_341_ = v_reuseFailAlloc_342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_341_;
            }
            3 => {
                if v_isShared_348_ == 0 {
                    v___x_350_ = v___x_347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
                    v___x_350_ = v_reuseFailAlloc_351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_353_: *mut LeanObject,
    mut v_decl_354_: *mut LeanObject,
    mut v_ref_355_: *mut LeanObject,
    mut v_a_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_357_: *mut LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_353_, v_decl_354_, v_ref_355_);
    lean_dec_ref(v_decl_354_);
    return v_res_357_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_381_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_382_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_383_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v___x_380_, v___x_381_, v___x_382_);
    return v___x_383_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(
    mut v_a_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_385_: *mut LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
    return v_res_385_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(
    mut v_m_386_: *mut LeanObject,
    mut v_e_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v_kind_388_ = lean_ctor_get(v_e_387_, 0);
    lean_inc(v_kind_388_);
    v___x_389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_kind_388_,
        v_e_387_,
        v_m_386_,
    );
    return v___x_389_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(
    mut v_es_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_array_mk(v_es_390_);
    return v___x_391_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_392_: *mut LeanObject,
    mut v_i_393_: usize,
    mut v_stop_394_: usize,
    mut v_b_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: usize = 0;
    let mut v___x_401_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_396_ = lean_usize_dec_eq(v_i_393_, v_stop_394_);
                if v___x_396_ == 0 {
                    v___x_397_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
                    v_kind_398_ = lean_ctor_get(v___x_397_, 0);
                    lean_inc(v___x_397_);
                    lean_inc(v_kind_398_);
                    v___x_399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_398_, v___x_397_, v_b_395_);
                    v___x_400_ = 1usize;
                    v___x_401_ = lean_usize_add(v_i_393_, v___x_400_);
                    v_i_393_ = v___x_401_;
                    v_b_395_ = v___x_399_;
                    state = 0;
                    continue;
                } else {
                    return v_b_395_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_403_: *mut LeanObject,
    mut v_i_404_: *mut LeanObject,
    mut v_stop_405_: *mut LeanObject,
    mut v_b_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_407_: usize = 0;
    let mut v_stop_boxed_408_: usize = 0;
    let mut v_res_409_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_407_ = lean_unbox_usize(v_i_404_);
    lean_dec(v_i_404_);
    v_stop_boxed_408_ = lean_unbox_usize(v_stop_405_);
    lean_dec(v_stop_405_);
    v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_403_, v_i_boxed_407_, v_stop_boxed_408_, v_b_406_);
    lean_dec_ref(v_as_403_);
    return v_res_409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_410_: *mut LeanObject,
    mut v_i_411_: usize,
    mut v_stop_412_: usize,
    mut v_b_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: usize = 0;
    let mut v___x_417_: usize = 0;
    let mut v___x_419_: u8 = 0;
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: u8 = 0;
    let mut v___x_425_: usize = 0;
    let mut v___x_426_: usize = 0;
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: usize = 0;
    let mut v___x_429_: usize = 0;
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_419_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
                if v___x_419_ == 0 {
                    v___x_420_ = lean_array_uget_borrowed(v_as_410_, v_i_411_);
                    v___x_421_ = lean_unsigned_to_nat(0);
                    v___x_422_ = lean_array_get_size(v___x_420_);
                    v___x_423_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
                    if v___x_423_ == 0 {
                        v___y_415_ = v_b_413_;
                        state = 1;
                        continue;
                    } else {
                        v___x_424_ = lean_nat_dec_le(v___x_422_, v___x_422_);
                        if v___x_424_ == 0 {
                            if v___x_423_ == 0 {
                                v___y_415_ = v_b_413_;
                                state = 1;
                                continue;
                            } else {
                                v___x_425_ = 0usize;
                                v___x_426_ = lean_usize_of_nat(v___x_422_);
                                v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_420_, v___x_425_, v___x_426_, v_b_413_);
                                v___y_415_ = v___x_427_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_428_ = 0usize;
                            v___x_429_ = lean_usize_of_nat(v___x_422_);
                            v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_420_, v___x_428_, v___x_429_, v_b_413_);
                            v___y_415_ = v___x_430_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_413_;
                }
            }
            1 => {
                v___x_416_ = 1usize;
                v___x_417_ = lean_usize_add(v_i_411_, v___x_416_);
                v_i_411_ = v___x_417_;
                v_b_413_ = v___y_415_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_431_: *mut LeanObject,
    mut v_i_432_: *mut LeanObject,
    mut v_stop_433_: *mut LeanObject,
    mut v_b_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_435_: usize = 0;
    let mut v_stop_boxed_436_: usize = 0;
    let mut v_res_437_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
    lean_dec(v_i_432_);
    v_stop_boxed_436_ = lean_unbox_usize(v_stop_433_);
    lean_dec(v_stop_433_);
    v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_431_, v_i_boxed_435_, v_stop_boxed_436_, v_b_434_);
    lean_dec_ref(v_as_431_);
    return v_res_437_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(
    mut v_initState_438_: *mut LeanObject,
    mut v_as_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    v___x_440_ = lean_unsigned_to_nat(0);
    v___x_441_ = lean_array_get_size(v_as_439_);
    v___x_442_ = lean_nat_dec_lt(v___x_440_, v___x_441_);
    if v___x_442_ == 0 {
        return v_initState_438_;
    } else {
        let mut v___x_443_: u8 = 0;
        v___x_443_ = lean_nat_dec_le(v___x_441_, v___x_441_);
        if v___x_443_ == 0 {
            if v___x_442_ == 0 {
                return v_initState_438_;
            } else {
                let mut v___x_444_: usize = 0;
                let mut v___x_445_: usize = 0;
                let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
                v___x_444_ = 0usize;
                v___x_445_ = lean_usize_of_nat(v___x_441_);
                v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_439_, v___x_444_, v___x_445_, v_initState_438_);
                return v___x_446_;
            }
        } else {
            let mut v___x_447_: usize = 0;
            let mut v___x_448_: usize = 0;
            let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
            v___x_447_ = 0usize;
            v___x_448_ = lean_usize_of_nat(v___x_441_);
            v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_439_, v___x_447_, v___x_448_, v_initState_438_);
            return v___x_449_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_450_: *mut LeanObject,
    mut v_as_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_452_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(v_initState_450_, v_as_451_);
    lean_dec_ref(v_as_451_);
    return v_res_452_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_;
    v___x_472_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_471_);
    return v___x_472_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(
    mut v_a_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_474_: *mut LeanObject = core::ptr::null_mut();
    v_res_474_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
    return v_res_474_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0;
    v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2;
    v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
    return v___x_480_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_482_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4;
    v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
    return v___x_483_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6;
    v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8;
    v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_491_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10;
    v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
    return v___x_492_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12;
    v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
    return v___x_495_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14;
    v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
    return v___x_498_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16;
    v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18;
    v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
    return v___x_504_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(
    mut v_stx_505_: *mut LeanObject,
    mut v___x_506_: *mut LeanObject,
    mut v_inst_507_: *mut LeanObject,
    mut v_inst_508_: *mut LeanObject,
    mut v_inst_509_: *mut LeanObject,
    mut v_inst_510_: *mut LeanObject,
    mut v_inst_511_: *mut LeanObject,
    mut v_macroStack_512_: *mut LeanObject,
    mut v_toPure_513_: *mut LeanObject,
    mut v_env_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v_before_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut v_unused_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v_before_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_before_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_unused_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut v_unused_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_602_: u8 = 0;
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_515_ = l_Lean_Elab_deprecatedSyntaxExt;
                v_toEnvExtension_516_ = lean_ctor_get(v___x_515_, 0);
                v_asyncMode_517_ = lean_ctor_get(v_toEnvExtension_516_, 2);
                lean_inc(v_stx_505_);
                v_kind_518_ = l_Lean_Syntax_getKind(v_stx_505_);
                v___x_603_ = lean_box(0);
                v___x_604_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_506_,
                    v___x_515_,
                    v_env_514_,
                    v_asyncMode_517_,
                    v___x_603_,
                );
                v___x_605_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_604_, v_kind_518_);
                lean_dec(v___x_604_);
                if lean_obj_tag(v___x_605_) == 1 {
                    lean_dec(v_toPure_513_);
                    v_val_606_ = lean_ctor_get(v___x_605_, 0);
                    lean_inc(v_val_606_);
                    lean_dec_ref_known(v___x_605_, 1);
                    v_text_x3f_607_ = lean_ctor_get(v_val_606_, 1);
                    lean_inc(v_text_x3f_607_);
                    lean_dec(v_val_606_);
                    if lean_obj_tag(v_text_x3f_607_) == 0 {
                        v___x_608_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once), _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
                        v___y_539_ = v___x_608_;
                        state = 2;
                        continue;
                    } else {
                        v_val_609_ = lean_ctor_get(v_text_x3f_607_, 0);
                        lean_inc(v_val_609_);
                        lean_dec_ref_known(v_text_x3f_607_, 1);
                        v___x_610_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once), _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19);
                        v___x_611_ = l_Lean_stringToMessageData(v_val_609_);
                        v___x_612_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_612_, 0, v___x_610_);
                        lean_ctor_set(v___x_612_, 1, v___x_611_);
                        v___y_539_ = v___x_612_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_605_);
                    lean_dec(v_kind_518_);
                    lean_dec(v_macroStack_512_);
                    lean_dec_ref(v_inst_511_);
                    lean_dec(v_inst_510_);
                    lean_dec(v_inst_509_);
                    lean_dec_ref(v_inst_508_);
                    lean_dec_ref(v_inst_507_);
                    lean_dec(v_stx_505_);
                    v___x_613_ = lean_box(0);
                    v___x_614_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_613_);
                    return v___x_614_;
                }
            }
            1 => {
                v___x_524_ = l_Lean_Linter_linter_deprecated_syntax;
                v___x_525_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1,
                );
                v___x_526_ = l_Lean_MessageData_ofName(v___y_521_);
                v___x_527_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_527_, 0, v___x_525_);
                lean_ctor_set(v___x_527_, 1, v___x_526_);
                v___x_528_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3,
                );
                v___x_529_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_529_, 0, v___x_527_);
                lean_ctor_set(v___x_529_, 1, v___x_528_);
                v___x_530_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_530_, 0, v___x_529_);
                lean_ctor_set(v___x_530_, 1, v___y_523_);
                v___x_531_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5,
                );
                v___x_532_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_532_, 0, v___x_530_);
                lean_ctor_set(v___x_532_, 1, v___x_531_);
                v___x_533_ = l_Lean_MessageData_ofName(v_kind_518_);
                v___x_534_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_534_, 0, v___x_532_);
                lean_ctor_set(v___x_534_, 1, v___x_533_);
                v___x_535_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_535_, 0, v___x_534_);
                lean_ctor_set(v___x_535_, 1, v___x_528_);
                v___x_536_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_536_, 0, v___x_535_);
                lean_ctor_set(v___x_536_, 1, v___y_520_);
                v___x_537_ = l_Lean_Linter_logLintIf___redArg(
                    v_inst_507_,
                    v_inst_508_,
                    v_inst_509_,
                    v_inst_510_,
                    v_inst_511_,
                    v___x_524_,
                    v___y_522_,
                    v___x_536_,
                );
                return v___x_537_;
            }
            2 => {
                if lean_obj_tag(v_macroStack_512_) == 0 {
                    v___x_540_ = l_Lean_Linter_linter_deprecated_syntax;
                    v___x_541_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7,
                    );
                    v___x_542_ = l_Lean_MessageData_ofName(v_kind_518_);
                    v___x_543_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_543_, 0, v___x_541_);
                    lean_ctor_set(v___x_543_, 1, v___x_542_);
                    v___x_544_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9,
                    );
                    v___x_545_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_545_, 0, v___x_543_);
                    lean_ctor_set(v___x_545_, 1, v___x_544_);
                    v___x_546_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_546_, 0, v___x_545_);
                    lean_ctor_set(v___x_546_, 1, v___y_539_);
                    v___x_547_ = l_Lean_Linter_logLintIf___redArg(
                        v_inst_507_,
                        v_inst_508_,
                        v_inst_509_,
                        v_inst_510_,
                        v_inst_511_,
                        v___x_540_,
                        v_stx_505_,
                        v___x_546_,
                    );
                    return v___x_547_;
                } else {
                    lean_dec(v_stx_505_);
                    v_head_548_ = lean_ctor_get(v_macroStack_512_, 0);
                    v_tail_549_ = lean_ctor_get(v_macroStack_512_, 1);
                    v_isSharedCheck_602_ = (!lean_is_exclusive(v_macroStack_512_)) as u8;
                    if v_isSharedCheck_602_ == 0 {
                        v___x_551_ = v_macroStack_512_;
                        v_isShared_552_ = v_isSharedCheck_602_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_tail_549_);
                        lean_inc(v_head_548_);
                        lean_dec(v_macroStack_512_);
                        v___x_551_ = lean_box(0);
                        v_isShared_552_ = v_isSharedCheck_602_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_tail_549_) == 0 {
                    v_before_553_ = lean_ctor_get(v_head_548_, 0);
                    v_isSharedCheck_574_ = (!lean_is_exclusive(v_head_548_)) as u8;
                    if v_isSharedCheck_574_ == 0 {
                        v_unused_575_ = lean_ctor_get(v_head_548_, 1);
                        lean_dec(v_unused_575_);
                        v___x_555_ = v_head_548_;
                        v_isShared_556_ = v_isSharedCheck_574_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_before_553_);
                        lean_dec(v_head_548_);
                        v___x_555_ = lean_box(0);
                        v_isShared_556_ = v_isSharedCheck_574_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_551_);
                    v_head_576_ = lean_ctor_get(v_tail_549_, 0);
                    v_isSharedCheck_600_ = (!lean_is_exclusive(v_tail_549_)) as u8;
                    if v_isSharedCheck_600_ == 0 {
                        v_unused_601_ = lean_ctor_get(v_tail_549_, 1);
                        lean_dec(v_unused_601_);
                        v___x_578_ = v_tail_549_;
                        v_isShared_579_ = v_isSharedCheck_600_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_head_576_);
                        lean_dec(v_tail_549_);
                        v___x_578_ = lean_box(0);
                        v_isShared_579_ = v_isSharedCheck_600_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_557_ = l_Lean_Linter_linter_deprecated_syntax;
                v___x_558_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1,
                );
                lean_inc(v_before_553_);
                v___x_559_ = l_Lean_Syntax_getKind(v_before_553_);
                v___x_560_ = l_Lean_MessageData_ofName(v___x_559_);
                if v_isShared_556_ == 0 {
                    lean_ctor_set_tag(v___x_555_, 7);
                    lean_ctor_set(v___x_555_, 1, v___x_560_);
                    lean_ctor_set(v___x_555_, 0, v___x_558_);
                    v___x_562_ = v___x_555_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_573_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_558_);
                    lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_560_);
                    v___x_562_ = v_reuseFailAlloc_573_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_563_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11,
                );
                if v_isShared_552_ == 0 {
                    lean_ctor_set_tag(v___x_551_, 7);
                    lean_ctor_set(v___x_551_, 1, v___x_563_);
                    lean_ctor_set(v___x_551_, 0, v___x_562_);
                    v___x_565_ = v___x_551_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_572_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_562_);
                    lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_563_);
                    v___x_565_ = v_reuseFailAlloc_572_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_566_ = l_Lean_MessageData_ofName(v_kind_518_);
                v___x_567_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_567_, 0, v___x_565_);
                lean_ctor_set(v___x_567_, 1, v___x_566_);
                v___x_568_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3,
                );
                v___x_569_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_569_, 0, v___x_567_);
                lean_ctor_set(v___x_569_, 1, v___x_568_);
                v___x_570_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_570_, 0, v___x_569_);
                lean_ctor_set(v___x_570_, 1, v___y_539_);
                v___x_571_ = l_Lean_Linter_logLintIf___redArg(
                    v_inst_507_,
                    v_inst_508_,
                    v_inst_509_,
                    v_inst_510_,
                    v_inst_511_,
                    v___x_557_,
                    v_before_553_,
                    v___x_570_,
                );
                return v___x_571_;
            }
            7 => {
                v_before_580_ = lean_ctor_get(v_head_548_, 0);
                lean_inc(v_before_580_);
                lean_dec(v_head_548_);
                v_before_581_ = lean_ctor_get(v_head_576_, 0);
                v_isSharedCheck_598_ = (!lean_is_exclusive(v_head_576_)) as u8;
                if v_isSharedCheck_598_ == 0 {
                    v_unused_599_ = lean_ctor_get(v_head_576_, 1);
                    lean_dec(v_unused_599_);
                    v___x_583_ = v_head_576_;
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_before_581_);
                    lean_dec(v_head_576_);
                    v___x_583_ = lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_585_ = l_Lean_Syntax_getKind(v_before_581_);
                lean_inc(v_before_580_);
                v___x_586_ = l_Lean_Syntax_getKind(v_before_580_);
                v___x_587_ = lean_name_eq(v___x_585_, v___x_586_);
                if v___x_587_ == 0 {
                    v___x_588_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13,
                    );
                    v___x_589_ = l_Lean_MessageData_ofName(v___x_585_);
                    if v_isShared_584_ == 0 {
                        lean_ctor_set_tag(v___x_583_, 7);
                        lean_ctor_set(v___x_583_, 1, v___x_589_);
                        lean_ctor_set(v___x_583_, 0, v___x_588_);
                        v___x_591_ = v___x_583_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_596_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_588_);
                        lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_589_);
                        v___x_591_ = v_reuseFailAlloc_596_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_585_);
                    lean_del_object(v___x_583_);
                    lean_del_object(v___x_578_);
                    v___x_597_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17,
                    );
                    v___y_520_ = v___y_539_;
                    v___y_521_ = v___x_586_;
                    v___y_522_ = v_before_580_;
                    v___y_523_ = v___x_597_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                v___x_592_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15,
                );
                if v_isShared_579_ == 0 {
                    lean_ctor_set_tag(v___x_578_, 7);
                    lean_ctor_set(v___x_578_, 1, v___x_592_);
                    lean_ctor_set(v___x_578_, 0, v___x_591_);
                    v___x_594_ = v___x_578_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_595_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_591_);
                    lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_592_);
                    v___x_594_ = v_reuseFailAlloc_595_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_520_ = v___y_539_;
                v___y_521_ = v___x_586_;
                v___y_522_ = v_before_580_;
                v___y_523_ = v___x_594_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax___redArg(
    mut v_inst_615_: *mut LeanObject,
    mut v_inst_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
    mut v_inst_618_: *mut LeanObject,
    mut v_inst_619_: *mut LeanObject,
    mut v_stx_620_: *mut LeanObject,
    mut v_macroStack_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_622_ = lean_ctor_get(v_inst_615_, 0);
    v_toBind_623_ = lean_ctor_get(v_inst_615_, 1);
    lean_inc(v_toBind_623_);
    v_getEnv_624_ = lean_ctor_get(v_inst_616_, 0);
    lean_inc(v_getEnv_624_);
    v_toPure_625_ = lean_ctor_get(v_toApplicative_622_, 1);
    lean_inc(v_toPure_625_);
    v___x_626_ = lean_box(1);
    v___f_627_ = lean_alloc_closure(
        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_627_, 0, v_stx_620_);
    lean_closure_set(v___f_627_, 1, v___x_626_);
    lean_closure_set(v___f_627_, 2, v_inst_615_);
    lean_closure_set(v___f_627_, 3, v_inst_617_);
    lean_closure_set(v___f_627_, 4, v_inst_619_);
    lean_closure_set(v___f_627_, 5, v_inst_618_);
    lean_closure_set(v___f_627_, 6, v_inst_616_);
    lean_closure_set(v___f_627_, 7, v_macroStack_621_);
    lean_closure_set(v___f_627_, 8, v_toPure_625_);
    v___x_628_ = lean_apply_4(
        v_toBind_623_,
        lean_box(0),
        lean_box(0),
        v_getEnv_624_,
        v___f_627_,
    );
    return v___x_628_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax(
    mut v_m_629_: *mut LeanObject,
    mut v_inst_630_: *mut LeanObject,
    mut v_inst_631_: *mut LeanObject,
    mut v_inst_632_: *mut LeanObject,
    mut v_inst_633_: *mut LeanObject,
    mut v_inst_634_: *mut LeanObject,
    mut v_inst_635_: *mut LeanObject,
    mut v_stx_636_: *mut LeanObject,
    mut v_macroStack_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lean_Elab_checkDeprecatedSyntax___redArg(
        v_inst_630_,
        v_inst_631_,
        v_inst_632_,
        v_inst_633_,
        v_inst_634_,
        v_stx_636_,
        v_macroStack_637_,
    );
    return v___x_638_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax___boxed(
    mut v_m_639_: *mut LeanObject,
    mut v_inst_640_: *mut LeanObject,
    mut v_inst_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
    mut v_inst_644_: *mut LeanObject,
    mut v_inst_645_: *mut LeanObject,
    mut v_stx_646_: *mut LeanObject,
    mut v_macroStack_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_648_: *mut LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Lean_Elab_checkDeprecatedSyntax(
        v_m_639_,
        v_inst_640_,
        v_inst_641_,
        v_inst_642_,
        v_inst_643_,
        v_inst_644_,
        v_inst_645_,
        v_stx_646_,
        v_macroStack_647_,
    );
    lean_dec_ref(v_inst_645_);
    return v_res_648_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_deprecated_syntax = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_deprecated_syntax);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_deprecatedSyntaxExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_deprecatedSyntaxExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeprecatedSyntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeprecatedSyntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DeprecatedSyntax(builtin);
}
