// Lean compiler output
// Module: Lean.Linter.EnvLinter.Nolint
// Imports: Lean.Attributes Init.Linter
use crate::r#gen::Init::Data::Array::Basic::{l_Array_contains___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Linter::{initialize_Init_Linter, runtime_initialize_Init_Linter};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_ParametricAttribute_getParam_x3f___redArg,
    l_Lean_registerParametricAttribute___redArg, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 110, 118, 76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [98, 117, 105, 108, 116, 105, 110, 78, 111, 108, 105, 110, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,5769806948869098747 as *mut LeanObject] };
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,6758588943529464673 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 110, 111, 108, 105, 110, 116, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,8152471842471720032 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [68, 111, 32, 110, 111, 116, 32, 114, 101, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 110, 32, 97, 110, 121, 32, 111, 102, 32, 116, 104, 101, 32, 116, 101, 115, 116, 115, 32, 111, 102, 32, 96, 108, 97, 107, 101, 32, 98, 117, 105, 108, 116, 105, 110, 45, 108, 105, 110, 116, 96, 0]};
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0_value:
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
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    v___x_189_ = lean_box(0);
    v___x_190_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_191_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_191_, 0, v___x_190_);
    lean_ctor_set(v___x_191_, 1, v___x_189_);
    return v___x_191_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    v___x_193_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0);
    v___x_194_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_194_, 0, v___x_193_);
    return v___x_194_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v___y_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_196_: *mut LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
    return v_res_196_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_197_: *mut LeanObject,
    mut v___y_198_: *mut LeanObject,
    mut v___y_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    v___x_201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
    return v___x_201_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_202_: *mut LeanObject,
    mut v___y_203_: *mut LeanObject,
    mut v___y_204_: *mut LeanObject,
    mut v___y_205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_206_: *mut LeanObject = core::ptr::null_mut();
    v_res_206_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0(v_00_u03b1_202_, v___y_203_, v___y_204_);
    lean_dec(v___y_204_);
    lean_dec_ref(v___y_203_);
    return v_res_206_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(
    mut v_x_207_: *mut LeanObject,
    mut v_x_208_: *mut LeanObject,
    mut v_x_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    v___x_212_ = lean_box(0);
    v___x_213_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_213_, 0, v___x_212_);
    return v___x_213_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(
    mut v_x_214_: *mut LeanObject,
    mut v_x_215_: *mut LeanObject,
    mut v_x_216_: *mut LeanObject,
    mut v___y_217_: *mut LeanObject,
    mut v___y_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_219_: *mut LeanObject = core::ptr::null_mut();
    v_res_219_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v_x_214_, v_x_215_, v_x_216_, v___y_217_);
    lean_dec(v___y_217_);
    lean_dec_ref(v_x_216_);
    lean_dec_ref(v_x_215_);
    lean_dec(v_x_214_);
    return v_res_219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(
    mut v_sz_220_: usize,
    mut v_i_221_: usize,
    mut v_bs_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_223_: u8 = 0;
    let mut v_v_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: usize = 0;
    let mut v___x_230_: usize = 0;
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_223_ = lean_usize_dec_lt(v_i_221_, v_sz_220_);
                if v___x_223_ == 0 {
                    return v_bs_222_;
                } else {
                    v_v_224_ = lean_array_uget(v_bs_222_, v_i_221_);
                    v___x_225_ = lean_unsigned_to_nat(0);
                    v_bs_x27_226_ = lean_array_uset(v_bs_222_, v_i_221_, v___x_225_);
                    v___x_227_ = l_Lean_TSyntax_getId(v_v_224_);
                    lean_dec(v_v_224_);
                    v___x_228_ = lean_erase_macro_scopes(v___x_227_);
                    v___x_229_ = 1usize;
                    v___x_230_ = lean_usize_add(v_i_221_, v___x_229_);
                    v___x_231_ = lean_array_uset(v_bs_x27_226_, v_i_221_, v___x_228_);
                    v_i_221_ = v___x_230_;
                    v_bs_222_ = v___x_231_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2___boxed(
    mut v_sz_233_: *mut LeanObject,
    mut v_i_234_: *mut LeanObject,
    mut v_bs_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_236_: usize = 0;
    let mut v_i_boxed_237_: usize = 0;
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_236_ = lean_unbox_usize(v_sz_233_);
    lean_dec(v_sz_233_);
    v_i_boxed_237_ = lean_unbox_usize(v_i_234_);
    lean_dec(v_i_234_);
    v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(v_sz_boxed_236_, v_i_boxed_237_, v_bs_235_);
    return v_res_238_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(
    mut v_sz_239_: usize,
    mut v_i_240_: usize,
    mut v_bs_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_242_: u8 = 0;
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: usize = 0;
    let mut v___x_248_: usize = 0;
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_242_ = lean_usize_dec_lt(v_i_240_, v_sz_239_);
                if v___x_242_ == 0 {
                    v___x_243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_243_, 0, v_bs_241_);
                    return v___x_243_;
                } else {
                    v_v_244_ = lean_array_uget(v_bs_241_, v_i_240_);
                    v___x_245_ = lean_unsigned_to_nat(0);
                    v_bs_x27_246_ = lean_array_uset(v_bs_241_, v_i_240_, v___x_245_);
                    v___x_247_ = 1usize;
                    v___x_248_ = lean_usize_add(v_i_240_, v___x_247_);
                    v___x_249_ = lean_array_uset(v_bs_x27_246_, v_i_240_, v_v_244_);
                    v_i_240_ = v___x_248_;
                    v_bs_241_ = v___x_249_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1___boxed(
    mut v_sz_251_: *mut LeanObject,
    mut v_i_252_: *mut LeanObject,
    mut v_bs_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_254_: usize = 0;
    let mut v_i_boxed_255_: usize = 0;
    let mut v_res_256_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_254_ = lean_unbox_usize(v_sz_251_);
    lean_dec(v_sz_251_);
    v_i_boxed_255_ = lean_unbox_usize(v_i_252_);
    lean_dec(v_i_252_);
    v_res_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(v_sz_boxed_254_, v_i_boxed_255_, v_bs_253_);
    return v_res_256_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(
    mut v___x_257_: *mut LeanObject,
    mut v_x_258_: *mut LeanObject,
    mut v_x_259_: *mut LeanObject,
    mut v___y_260_: *mut LeanObject,
    mut v___y_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_268_: usize = 0;
    let mut v___x_269_: usize = 0;
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_275_: u8 = 0;
    let mut v_sz_276_: usize = 0;
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_x_259_);
                v___x_263_ = l_Lean_Syntax_isOfKind(v_x_259_, v___x_257_);
                if v___x_263_ == 0 {
                    lean_dec(v_x_259_);
                    v___x_264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
                    return v___x_264_;
                } else {
                    v___x_265_ = lean_unsigned_to_nat(1);
                    v___x_266_ = l_Lean_Syntax_getArg(v_x_259_, v___x_265_);
                    lean_dec(v_x_259_);
                    v___x_267_ = l_Lean_Syntax_getArgs(v___x_266_);
                    lean_dec(v___x_266_);
                    v_sz_268_ = lean_array_size(v___x_267_);
                    v___x_269_ = 0usize;
                    v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(v_sz_268_, v___x_269_, v___x_267_);
                    if lean_obj_tag(v___x_270_) == 0 {
                        v___x_271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
                        return v___x_271_;
                    } else {
                        v_val_272_ = lean_ctor_get(v___x_270_, 0);
                        v_isSharedCheck_281_ = (!lean_is_exclusive(v___x_270_)) as u8;
                        if v_isSharedCheck_281_ == 0 {
                            v___x_274_ = v___x_270_;
                            v_isShared_275_ = v_isSharedCheck_281_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_272_);
                            lean_dec(v___x_270_);
                            v___x_274_ = lean_box(0);
                            v_isShared_275_ = v_isSharedCheck_281_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_276_ = lean_array_size(v_val_272_);
                v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(v_sz_276_, v___x_269_, v_val_272_);
                if v_isShared_275_ == 0 {
                    lean_ctor_set_tag(v___x_274_, 0);
                    lean_ctor_set(v___x_274_, 0, v___x_277_);
                    v___x_279_ = v___x_274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
                    v___x_279_ = v_reuseFailAlloc_280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(
    mut v___x_282_: *mut LeanObject,
    mut v_x_283_: *mut LeanObject,
    mut v_x_284_: *mut LeanObject,
    mut v___y_285_: *mut LeanObject,
    mut v___y_286_: *mut LeanObject,
    mut v___y_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_288_: *mut LeanObject = core::ptr::null_mut();
    v_res_288_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v___x_282_, v_x_283_, v_x_284_, v___y_285_, v___y_286_);
    lean_dec(v___y_286_);
    lean_dec_ref(v___y_285_);
    lean_dec(v_x_283_);
    lean_dec(v___x_282_);
    return v_res_288_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(
    mut v___x_289_: u8,
    mut v_env_290_: *mut LeanObject,
    mut v_n_291_: *mut LeanObject,
    mut v_x_292_: *mut LeanObject,
) -> u8 {
    let mut v___x_293_: u8 = 0;
    v___x_293_ = l_Lean_Environment_contains(v_env_290_, v_n_291_, v___x_289_);
    return v___x_293_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(
    mut v___x_294_: *mut LeanObject,
    mut v_env_295_: *mut LeanObject,
    mut v_n_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_779__boxed_298_: u8 = 0;
    let mut v_res_299_: u8 = 0;
    let mut v_r_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_779__boxed_298_ = (lean_unbox(v___x_294_) as u8);
    v_res_299_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v___x_779__boxed_298_, v_env_295_, v_n_296_, v_x_297_);
    lean_dec_ref(v_x_297_);
    v_r_300_ = lean_box((v_res_299_) as usize);
    return v_r_300_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_;
    v___x_333_ = l_Lean_registerParametricAttribute___redArg(v___x_332_);
    return v___x_333_;
}
pub unsafe fn l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(
    mut v_a_334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_335_: *mut LeanObject = core::ptr::null_mut();
    v_res_335_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_();
    return v_res_335_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0(
    mut v___x_338_: *mut LeanObject,
    mut v_linter_339_: *mut LeanObject,
    mut v_toPure_340_: *mut LeanObject,
    mut v___x_341_: *mut LeanObject,
    mut v_decl_342_: *mut LeanObject,
    mut v_____do__lift_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: u8 = 0;
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: u8 = 0;
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_356_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_353_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
                v___x_354_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                    v___x_341_,
                    v___x_353_,
                    v_____do__lift_343_,
                    v_decl_342_,
                );
                if lean_obj_tag(v___x_354_) == 0 {
                    v___x_355_ =
                        l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0;
                    v___y_345_ = v___x_355_;
                    state = 1;
                    continue;
                } else {
                    v_val_356_ = lean_ctor_get(v___x_354_, 0);
                    lean_inc(v_val_356_);
                    lean_dec_ref_known(v___x_354_, 1);
                    v___y_345_ = v_val_356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_346_ = l_Array_contains___redArg(v___x_338_, v___y_345_, v_linter_339_);
                if v___x_346_ == 0 {
                    v___x_347_ = 1;
                    v___x_348_ = lean_box((v___x_347_) as usize);
                    v___x_349_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_348_);
                    return v___x_349_;
                } else {
                    v___x_350_ = 0;
                    v___x_351_ = lean_box((v___x_350_) as usize);
                    v___x_352_ = lean_apply_2(v_toPure_340_, lean_box(0), v___x_351_);
                    return v___x_352_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1() -> *mut LeanObject
{
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = l_Array_instInhabited(lean_box(0));
    return v___x_358_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted___redArg(
    mut v_inst_359_: *mut LeanObject,
    mut v_inst_360_: *mut LeanObject,
    mut v_linter_361_: *mut LeanObject,
    mut v_decl_362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_363_ = lean_ctor_get(v_inst_359_, 0);
    lean_inc_ref(v_toApplicative_363_);
    v_toBind_364_ = lean_ctor_get(v_inst_359_, 1);
    lean_inc(v_toBind_364_);
    lean_dec_ref(v_inst_359_);
    v_getEnv_365_ = lean_ctor_get(v_inst_360_, 0);
    lean_inc(v_getEnv_365_);
    lean_dec_ref(v_inst_360_);
    v_toPure_366_ = lean_ctor_get(v_toApplicative_363_, 1);
    lean_inc(v_toPure_366_);
    lean_dec_ref(v_toApplicative_363_);
    v___x_367_ = l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0;
    v___x_368_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1_once),
        _init_l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1,
    );
    v___f_369_ = lean_alloc_closure(
        l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_369_, 0, v___x_367_);
    lean_closure_set(v___f_369_, 1, v_linter_361_);
    lean_closure_set(v___f_369_, 2, v_toPure_366_);
    lean_closure_set(v___f_369_, 3, v___x_368_);
    lean_closure_set(v___f_369_, 4, v_decl_362_);
    v___x_370_ = lean_apply_4(
        v_toBind_364_,
        lean_box(0),
        lean_box(0),
        v_getEnv_365_,
        v___f_369_,
    );
    return v___x_370_;
}
pub unsafe fn l_Lean_Linter_EnvLinter_shouldBeLinted(
    mut v_m_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_linter_374_: *mut LeanObject,
    mut v_decl_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Lean_Linter_EnvLinter_shouldBeLinted___redArg(
        v_inst_372_,
        v_inst_373_,
        v_linter_374_,
        v_decl_375_,
    );
    return v___x_376_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Linter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_EnvLinter_builtinNolintAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_EnvLinter_builtinNolintAttr);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_EnvLinter_Nolint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_EnvLinter_Nolint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Linter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_EnvLinter_Nolint(builtin);
}
