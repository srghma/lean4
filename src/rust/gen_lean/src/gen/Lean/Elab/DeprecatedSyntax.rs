// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax
// Imports: Lean.MonadEnv Lean.Linter.Init Lean.Elab.Util
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_uget_borrowed, lean_name_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Prelude::l_Lean_Syntax_getKind;
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
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13546154976408593379 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1829946577588164054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 119, 104, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 105, 115, 32, 117, 115, 101, 100, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14679817356290926072 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9479425830589914185 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_linter_deprecated_syntax: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 83, 121, 110, 116, 97, 120, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16340096650070628312 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_deprecatedSyntaxExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value:
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
    m_data: [109, 97, 99, 114, 111, 32, 39, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value:
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
    m_data: [115, 121, 110, 116, 97, 120, 32, 39, 0],
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(
    mut v_name_325_: *mut crate::leanh::LeanObject,
    mut v_decl_326_: *mut crate::leanh::LeanObject,
    mut v_ref_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_343_: u8 = 0;
    let mut v_unused_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_348_: u8 = 0;
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_329_ = crate::leanh::lean_ctor_get(v_decl_326_, 0);
                v_descr_330_ = crate::leanh::lean_ctor_get(v_decl_326_, 1);
                v_deprecation_x3f_331_ = crate::leanh::lean_ctor_get(v_decl_326_, 2);
                v___x_332_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_333_ = (crate::leanh::lean_unbox(v_defValue_329_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_332_, 0 as u32, v___x_333_);
                crate::leanh::lean_inc(v_deprecation_x3f_331_);
                crate::leanh::lean_inc_ref(v_descr_330_);
                crate::leanh::lean_inc_n(v_name_325_, 2);
                v___x_334_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_334_, 0, v_name_325_);
                crate::leanh::lean_ctor_set(v___x_334_, 1, v_ref_327_);
                crate::leanh::lean_ctor_set(v___x_334_, 2, v___x_332_);
                crate::leanh::lean_ctor_set(v___x_334_, 3, v_descr_330_);
                crate::leanh::lean_ctor_set(v___x_334_, 4, v_deprecation_x3f_331_);
                v___x_335_ = lean_register_option(v_name_325_, v___x_334_);
                if crate::leanh::lean_obj_tag(v___x_335_) == 0 {
                    v_isSharedCheck_343_ = (!crate::leanh::lean_is_exclusive(v___x_335_)) as u8;
                    if v_isSharedCheck_343_ == 0 {
                        v_unused_344_ = crate::leanh::lean_ctor_get(v___x_335_, 0);
                        crate::leanh::lean_dec(v_unused_344_);
                        v___x_337_ = v___x_335_;
                        v_isShared_338_ = v_isSharedCheck_343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_335_);
                        v___x_337_ = crate::leanh::lean_box(0);
                        v_isShared_338_ = v_isSharedCheck_343_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_325_);
                    v_a_345_ = crate::leanh::lean_ctor_get(v___x_335_, 0);
                    v_isSharedCheck_352_ = (!crate::leanh::lean_is_exclusive(v___x_335_)) as u8;
                    if v_isSharedCheck_352_ == 0 {
                        v___x_347_ = v___x_335_;
                        v_isShared_348_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_345_);
                        crate::leanh::lean_dec(v___x_335_);
                        v___x_347_ = crate::leanh::lean_box(0);
                        v_isShared_348_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_329_);
                v___x_339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_339_, 0, v_name_325_);
                crate::leanh::lean_ctor_set(v___x_339_, 1, v_defValue_329_);
                if v_isShared_338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_337_, 0, v___x_339_);
                    v___x_341_ = v___x_337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
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
                    v_reuseFailAlloc_351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
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
    mut v_name_353_: *mut crate::leanh::LeanObject,
    mut v_decl_354_: *mut crate::leanh::LeanObject,
    mut v_ref_355_: *mut crate::leanh::LeanObject,
    mut v_a_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_353_, v_decl_354_, v_ref_355_);
    crate::leanh::lean_dec_ref(v_decl_354_);
    return v_res_357_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_381_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_382_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_;
    v___x_383_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v___x_380_, v___x_381_, v___x_382_);
    return v___x_383_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(
    mut v_a_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
    return v_res_385_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(
    mut v_m_386_: *mut crate::leanh::LeanObject,
    mut v_e_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_388_ = crate::leanh::lean_ctor_get(v_e_387_, 0);
    crate::leanh::lean_inc(v_kind_388_);
    v___x_389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_kind_388_,
        v_e_387_,
        v_m_386_,
    );
    return v___x_389_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(
    mut v_es_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_array_mk(v_es_390_);
    return v___x_391_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_392_: *mut crate::leanh::LeanObject,
    mut v_i_393_: usize,
    mut v_stop_394_: usize,
    mut v_b_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: usize = 0;
    let mut v___x_401_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_396_ = lean_usize_dec_eq(v_i_393_, v_stop_394_);
                if v___x_396_ == 0 {
                    v___x_397_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
                    v_kind_398_ = crate::leanh::lean_ctor_get(v___x_397_, 0);
                    crate::leanh::lean_inc(v___x_397_);
                    crate::leanh::lean_inc(v_kind_398_);
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
    mut v_as_403_: *mut crate::leanh::LeanObject,
    mut v_i_404_: *mut crate::leanh::LeanObject,
    mut v_stop_405_: *mut crate::leanh::LeanObject,
    mut v_b_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_407_: usize = 0;
    let mut v_stop_boxed_408_: usize = 0;
    let mut v_res_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_407_ = crate::leanh::lean_unbox_usize(v_i_404_);
    crate::leanh::lean_dec(v_i_404_);
    v_stop_boxed_408_ = crate::leanh::lean_unbox_usize(v_stop_405_);
    crate::leanh::lean_dec(v_stop_405_);
    v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_403_, v_i_boxed_407_, v_stop_boxed_408_, v_b_406_);
    crate::leanh::lean_dec_ref(v_as_403_);
    return v_res_409_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_410_: *mut crate::leanh::LeanObject,
    mut v_i_411_: usize,
    mut v_stop_412_: usize,
    mut v_b_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: usize = 0;
    let mut v___x_417_: usize = 0;
    let mut v___x_419_: u8 = 0;
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: u8 = 0;
    let mut v___x_425_: usize = 0;
    let mut v___x_426_: usize = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: usize = 0;
    let mut v___x_429_: usize = 0;
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_419_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
                if v___x_419_ == 0 {
                    v___x_420_ = lean_array_uget_borrowed(v_as_410_, v_i_411_);
                    v___x_421_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_as_431_: *mut crate::leanh::LeanObject,
    mut v_i_432_: *mut crate::leanh::LeanObject,
    mut v_stop_433_: *mut crate::leanh::LeanObject,
    mut v_b_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_435_: usize = 0;
    let mut v_stop_boxed_436_: usize = 0;
    let mut v_res_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_435_ = crate::leanh::lean_unbox_usize(v_i_432_);
    crate::leanh::lean_dec(v_i_432_);
    v_stop_boxed_436_ = crate::leanh::lean_unbox_usize(v_stop_433_);
    crate::leanh::lean_dec(v_stop_433_);
    v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_431_, v_i_boxed_435_, v_stop_boxed_436_, v_b_434_);
    crate::leanh::lean_dec_ref(v_as_431_);
    return v_res_437_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(
    mut v_initState_438_: *mut crate::leanh::LeanObject,
    mut v_as_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    v___x_440_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_444_ = 0usize;
                v___x_445_ = lean_usize_of_nat(v___x_441_);
                v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_439_, v___x_444_, v___x_445_, v_initState_438_);
                return v___x_446_;
            }
        } else {
            let mut v___x_447_: usize = 0;
            let mut v___x_448_: usize = 0;
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_447_ = 0usize;
            v___x_448_ = lean_usize_of_nat(v___x_441_);
            v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_439_, v___x_447_, v___x_448_, v_initState_438_);
            return v___x_449_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_450_: *mut crate::leanh::LeanObject,
    mut v_as_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(v_initState_450_, v_as_451_);
    crate::leanh::lean_dec_ref(v_as_451_);
    return v_res_452_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_;
    v___x_472_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_471_);
    return v___x_472_;
}
pub unsafe fn l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(
    mut v_a_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
    return v_res_474_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0;
    v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2;
    v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
    return v___x_480_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_482_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4;
    v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
    return v___x_483_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6;
    v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8;
    v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_491_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10;
    v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
    return v___x_492_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12;
    v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
    return v___x_495_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_497_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14;
    v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
    return v___x_498_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16;
    v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18;
    v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
    return v___x_504_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(
    mut v_stx_505_: *mut crate::leanh::LeanObject,
    mut v___x_506_: *mut crate::leanh::LeanObject,
    mut v_inst_507_: *mut crate::leanh::LeanObject,
    mut v_inst_508_: *mut crate::leanh::LeanObject,
    mut v_inst_509_: *mut crate::leanh::LeanObject,
    mut v_inst_510_: *mut crate::leanh::LeanObject,
    mut v_inst_511_: *mut crate::leanh::LeanObject,
    mut v_macroStack_512_: *mut crate::leanh::LeanObject,
    mut v_toPure_513_: *mut crate::leanh::LeanObject,
    mut v_env_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v_before_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut v_unused_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v_before_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_before_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_unused_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut v_unused_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_602_: u8 = 0;
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_515_ = l_Lean_Elab_deprecatedSyntaxExt;
                v_toEnvExtension_516_ = crate::leanh::lean_ctor_get(v___x_515_, 0);
                v_asyncMode_517_ = crate::leanh::lean_ctor_get(v_toEnvExtension_516_, 2);
                crate::leanh::lean_inc(v_stx_505_);
                v_kind_518_ = l_Lean_Syntax_getKind(v_stx_505_);
                v___x_603_ = crate::leanh::lean_box(0);
                v___x_604_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_506_,
                    v___x_515_,
                    v_env_514_,
                    v_asyncMode_517_,
                    v___x_603_,
                );
                v___x_605_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_604_, v_kind_518_);
                crate::leanh::lean_dec(v___x_604_);
                if crate::leanh::lean_obj_tag(v___x_605_) == 1 {
                    crate::leanh::lean_dec(v_toPure_513_);
                    v_val_606_ = crate::leanh::lean_ctor_get(v___x_605_, 0);
                    crate::leanh::lean_inc(v_val_606_);
                    crate::leanh::lean_dec_ref_known(v___x_605_, 1);
                    v_text_x3f_607_ = crate::leanh::lean_ctor_get(v_val_606_, 1);
                    crate::leanh::lean_inc(v_text_x3f_607_);
                    crate::leanh::lean_dec(v_val_606_);
                    if crate::leanh::lean_obj_tag(v_text_x3f_607_) == 0 {
                        v___x_608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once), _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
                        v___y_539_ = v___x_608_;
                        state = 2;
                        continue;
                    } else {
                        v_val_609_ = crate::leanh::lean_ctor_get(v_text_x3f_607_, 0);
                        crate::leanh::lean_inc(v_val_609_);
                        crate::leanh::lean_dec_ref_known(v_text_x3f_607_, 1);
                        v___x_610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once), _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19);
                        v___x_611_ = l_Lean_stringToMessageData(v_val_609_);
                        v___x_612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_612_, 0, v___x_610_);
                        crate::leanh::lean_ctor_set(v___x_612_, 1, v___x_611_);
                        v___y_539_ = v___x_612_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_605_);
                    crate::leanh::lean_dec(v_kind_518_);
                    crate::leanh::lean_dec(v_macroStack_512_);
                    crate::leanh::lean_dec_ref(v_inst_511_);
                    crate::leanh::lean_dec(v_inst_510_);
                    crate::leanh::lean_dec(v_inst_509_);
                    crate::leanh::lean_dec_ref(v_inst_508_);
                    crate::leanh::lean_dec_ref(v_inst_507_);
                    crate::leanh::lean_dec(v_stx_505_);
                    v___x_613_ = crate::leanh::lean_box(0);
                    v___x_614_ = crate::leanh::lean_apply_2(
                        v_toPure_513_,
                        crate::leanh::lean_box(0),
                        v___x_613_,
                    );
                    return v___x_614_;
                }
            }
            1 => {
                v___x_524_ = l_Lean_Linter_linter_deprecated_syntax;
                v___x_525_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1,
                );
                v___x_526_ = l_Lean_MessageData_ofName(v___y_521_);
                v___x_527_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_527_, 0, v___x_525_);
                crate::leanh::lean_ctor_set(v___x_527_, 1, v___x_526_);
                v___x_528_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3,
                );
                v___x_529_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_529_, 0, v___x_527_);
                crate::leanh::lean_ctor_set(v___x_529_, 1, v___x_528_);
                v___x_530_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
                crate::leanh::lean_ctor_set(v___x_530_, 1, v___y_523_);
                v___x_531_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5,
                );
                v___x_532_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_530_);
                crate::leanh::lean_ctor_set(v___x_532_, 1, v___x_531_);
                v___x_533_ = l_Lean_MessageData_ofName(v_kind_518_);
                v___x_534_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_534_, 0, v___x_532_);
                crate::leanh::lean_ctor_set(v___x_534_, 1, v___x_533_);
                v___x_535_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_535_, 0, v___x_534_);
                crate::leanh::lean_ctor_set(v___x_535_, 1, v___x_528_);
                v___x_536_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                crate::leanh::lean_ctor_set(v___x_536_, 1, v___y_520_);
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
                if crate::leanh::lean_obj_tag(v_macroStack_512_) == 0 {
                    v___x_540_ = l_Lean_Linter_linter_deprecated_syntax;
                    v___x_541_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7,
                    );
                    v___x_542_ = l_Lean_MessageData_ofName(v_kind_518_);
                    v___x_543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_541_);
                    crate::leanh::lean_ctor_set(v___x_543_, 1, v___x_542_);
                    v___x_544_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9,
                    );
                    v___x_545_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_543_);
                    crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_544_);
                    v___x_546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_546_, 0, v___x_545_);
                    crate::leanh::lean_ctor_set(v___x_546_, 1, v___y_539_);
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
                    crate::leanh::lean_dec(v_stx_505_);
                    v_head_548_ = crate::leanh::lean_ctor_get(v_macroStack_512_, 0);
                    v_tail_549_ = crate::leanh::lean_ctor_get(v_macroStack_512_, 1);
                    v_isSharedCheck_602_ =
                        (!crate::leanh::lean_is_exclusive(v_macroStack_512_)) as u8;
                    if v_isSharedCheck_602_ == 0 {
                        v___x_551_ = v_macroStack_512_;
                        v_isShared_552_ = v_isSharedCheck_602_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_549_);
                        crate::leanh::lean_inc(v_head_548_);
                        crate::leanh::lean_dec(v_macroStack_512_);
                        v___x_551_ = crate::leanh::lean_box(0);
                        v_isShared_552_ = v_isSharedCheck_602_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_tail_549_) == 0 {
                    v_before_553_ = crate::leanh::lean_ctor_get(v_head_548_, 0);
                    v_isSharedCheck_574_ = (!crate::leanh::lean_is_exclusive(v_head_548_)) as u8;
                    if v_isSharedCheck_574_ == 0 {
                        v_unused_575_ = crate::leanh::lean_ctor_get(v_head_548_, 1);
                        crate::leanh::lean_dec(v_unused_575_);
                        v___x_555_ = v_head_548_;
                        v_isShared_556_ = v_isSharedCheck_574_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_before_553_);
                        crate::leanh::lean_dec(v_head_548_);
                        v___x_555_ = crate::leanh::lean_box(0);
                        v_isShared_556_ = v_isSharedCheck_574_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_551_);
                    v_head_576_ = crate::leanh::lean_ctor_get(v_tail_549_, 0);
                    v_isSharedCheck_600_ = (!crate::leanh::lean_is_exclusive(v_tail_549_)) as u8;
                    if v_isSharedCheck_600_ == 0 {
                        v_unused_601_ = crate::leanh::lean_ctor_get(v_tail_549_, 1);
                        crate::leanh::lean_dec(v_unused_601_);
                        v___x_578_ = v_tail_549_;
                        v_isShared_579_ = v_isSharedCheck_600_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_576_);
                        crate::leanh::lean_dec(v_tail_549_);
                        v___x_578_ = crate::leanh::lean_box(0);
                        v_isShared_579_ = v_isSharedCheck_600_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_557_ = l_Lean_Linter_linter_deprecated_syntax;
                v___x_558_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1,
                );
                crate::leanh::lean_inc(v_before_553_);
                v___x_559_ = l_Lean_Syntax_getKind(v_before_553_);
                v___x_560_ = l_Lean_MessageData_ofName(v___x_559_);
                if v_isShared_556_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_555_, 7);
                    crate::leanh::lean_ctor_set(v___x_555_, 1, v___x_560_);
                    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_558_);
                    v___x_562_ = v___x_555_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_573_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_560_);
                    v___x_562_ = v_reuseFailAlloc_573_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_563_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11,
                );
                if v_isShared_552_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_551_, 7);
                    crate::leanh::lean_ctor_set(v___x_551_, 1, v___x_563_);
                    crate::leanh::lean_ctor_set(v___x_551_, 0, v___x_562_);
                    v___x_565_ = v___x_551_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_572_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_563_);
                    v___x_565_ = v_reuseFailAlloc_572_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_566_ = l_Lean_MessageData_ofName(v_kind_518_);
                v___x_567_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_567_, 0, v___x_565_);
                crate::leanh::lean_ctor_set(v___x_567_, 1, v___x_566_);
                v___x_568_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3,
                );
                v___x_569_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_569_, 0, v___x_567_);
                crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_568_);
                v___x_570_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_570_, 0, v___x_569_);
                crate::leanh::lean_ctor_set(v___x_570_, 1, v___y_539_);
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
                v_before_580_ = crate::leanh::lean_ctor_get(v_head_548_, 0);
                crate::leanh::lean_inc(v_before_580_);
                crate::leanh::lean_dec(v_head_548_);
                v_before_581_ = crate::leanh::lean_ctor_get(v_head_576_, 0);
                v_isSharedCheck_598_ = (!crate::leanh::lean_is_exclusive(v_head_576_)) as u8;
                if v_isSharedCheck_598_ == 0 {
                    v_unused_599_ = crate::leanh::lean_ctor_get(v_head_576_, 1);
                    crate::leanh::lean_dec(v_unused_599_);
                    v___x_583_ = v_head_576_;
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_581_);
                    crate::leanh::lean_dec(v_head_576_);
                    v___x_583_ = crate::leanh::lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_585_ = l_Lean_Syntax_getKind(v_before_581_);
                crate::leanh::lean_inc(v_before_580_);
                v___x_586_ = l_Lean_Syntax_getKind(v_before_580_);
                v___x_587_ = lean_name_eq(v___x_585_, v___x_586_);
                if v___x_587_ == 0 {
                    v___x_588_ = crate::leanh::lean_obj_once(
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
                        crate::leanh::lean_ctor_set_tag(v___x_583_, 7);
                        crate::leanh::lean_ctor_set(v___x_583_, 1, v___x_589_);
                        crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_588_);
                        v___x_591_ = v___x_583_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_588_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_589_);
                        v___x_591_ = v_reuseFailAlloc_596_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_585_);
                    crate::leanh::lean_del_object(v___x_583_);
                    crate::leanh::lean_del_object(v___x_578_);
                    v___x_597_ = crate::leanh::lean_obj_once(
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
                v___x_592_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once
                    ),
                    _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15,
                );
                if v_isShared_579_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_578_, 7);
                    crate::leanh::lean_ctor_set(v___x_578_, 1, v___x_592_);
                    crate::leanh::lean_ctor_set(v___x_578_, 0, v___x_591_);
                    v___x_594_ = v___x_578_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_595_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_592_);
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
    mut v_inst_615_: *mut crate::leanh::LeanObject,
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_inst_618_: *mut crate::leanh::LeanObject,
    mut v_inst_619_: *mut crate::leanh::LeanObject,
    mut v_stx_620_: *mut crate::leanh::LeanObject,
    mut v_macroStack_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_622_ = crate::leanh::lean_ctor_get(v_inst_615_, 0);
    v_toBind_623_ = crate::leanh::lean_ctor_get(v_inst_615_, 1);
    crate::leanh::lean_inc(v_toBind_623_);
    v_getEnv_624_ = crate::leanh::lean_ctor_get(v_inst_616_, 0);
    crate::leanh::lean_inc(v_getEnv_624_);
    v_toPure_625_ = crate::leanh::lean_ctor_get(v_toApplicative_622_, 1);
    crate::leanh::lean_inc(v_toPure_625_);
    v___x_626_ = crate::leanh::lean_box(1);
    v___f_627_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_627_, 0, v_stx_620_);
    crate::leanh::lean_closure_set(v___f_627_, 1, v___x_626_);
    crate::leanh::lean_closure_set(v___f_627_, 2, v_inst_615_);
    crate::leanh::lean_closure_set(v___f_627_, 3, v_inst_617_);
    crate::leanh::lean_closure_set(v___f_627_, 4, v_inst_619_);
    crate::leanh::lean_closure_set(v___f_627_, 5, v_inst_618_);
    crate::leanh::lean_closure_set(v___f_627_, 6, v_inst_616_);
    crate::leanh::lean_closure_set(v___f_627_, 7, v_macroStack_621_);
    crate::leanh::lean_closure_set(v___f_627_, 8, v_toPure_625_);
    v___x_628_ = crate::leanh::lean_apply_4(
        v_toBind_623_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_624_,
        v___f_627_,
    );
    return v___x_628_;
}
pub unsafe fn l_Lean_Elab_checkDeprecatedSyntax(
    mut v_m_629_: *mut crate::leanh::LeanObject,
    mut v_inst_630_: *mut crate::leanh::LeanObject,
    mut v_inst_631_: *mut crate::leanh::LeanObject,
    mut v_inst_632_: *mut crate::leanh::LeanObject,
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
    mut v_inst_635_: *mut crate::leanh::LeanObject,
    mut v_stx_636_: *mut crate::leanh::LeanObject,
    mut v_macroStack_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_639_: *mut crate::leanh::LeanObject,
    mut v_inst_640_: *mut crate::leanh::LeanObject,
    mut v_inst_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_inst_643_: *mut crate::leanh::LeanObject,
    mut v_inst_644_: *mut crate::leanh::LeanObject,
    mut v_inst_645_: *mut crate::leanh::LeanObject,
    mut v_stx_646_: *mut crate::leanh::LeanObject,
    mut v_macroStack_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_645_);
    return v_res_648_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeprecatedSyntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_deprecated_syntax = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_deprecated_syntax);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_deprecatedSyntaxExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_deprecatedSyntaxExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeprecatedSyntax(
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
pub unsafe fn initialize_Lean_Elab_DeprecatedSyntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeprecatedSyntax(builtin);
}
