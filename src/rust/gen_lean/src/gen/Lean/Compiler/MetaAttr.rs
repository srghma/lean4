// Lean compiler output
// Module: Lean.Compiler.MetaAttr
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Prelude::l_instInhabitedOfMonad___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_isCtor;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed,
    l_Lean_TagDeclarationExtension_isTagged, l_Lean_TagDeclarationExtension_tag,
    l_Lean_mkTagDeclarationExtension, l_Lean_registerSimplePersistentEnvExtension___redArg,
    runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
};
use crate::ffi::lean_array_fswap;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
};
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 101, 116, 97, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11357144685004083879 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3685092993381856794 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1296340425502547387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 116, 97, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11419987284942455500 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_NameSet_insert as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 77, 101, 116, 97, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14288846686841754723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_isDeclMeta___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isDeclMeta___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isDeclMeta___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isDeclMeta___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 98, 111, 120, 101, 100, 0],
    };
static mut l_Lean_isDeclMeta___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isDeclMeta___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getIRPhases_spec__0___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_getIRPhases_spec__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_getIRPhases_spec__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getIRPhases___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Lean_getIRPhases___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getIRPhases___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getIRPhases___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Lean_getIRPhases___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getIRPhases___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getIRPhases___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_getIRPhases___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getIRPhases___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getIRPhases___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getIRPhases___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_;
    v___x_414_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_;
    v___x_415_ = l_Lean_mkTagDeclarationExtension(v___x_413_, v___x_414_);
    return v___x_415_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2____boxed(
    mut v_a_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
    return v_res_417_;
}
pub unsafe fn l_Lean_markMeta(
    mut v_env_418_: *mut crate::leanh::LeanObject,
    mut v_declName_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
    v___x_421_ = l_Lean_TagDeclarationExtension_tag(v___x_420_, v_env_418_, v_declName_419_);
    return v___x_421_;
}
pub unsafe fn l_Lean_isMarkedMeta(
    mut v_env_422_: *mut crate::leanh::LeanObject,
    mut v_declName_423_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: u8 = 0;
    v___x_424_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
    v_toEnvExtension_425_ = crate::leanh::lean_ctor_get(v___x_424_, 0);
    v_asyncMode_426_ = crate::leanh::lean_ctor_get(v_toEnvExtension_425_, 2);
    v___x_427_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_424_,
        v_env_422_,
        v_declName_423_,
        v_asyncMode_426_,
    );
    return v___x_427_;
}
pub unsafe fn l_Lean_isMarkedMeta___boxed(
    mut v_env_428_: *mut crate::leanh::LeanObject,
    mut v_declName_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_isMarkedMeta(v_env_428_, v_declName_429_);
    v_r_431_ = crate::leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(
    mut v_x_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = l_Lean_NameSet_empty;
    return v___x_433_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(
    mut v_x_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x_434_);
    crate::leanh::lean_dec_ref(v_x_434_);
    return v_res_435_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(
    mut v_es_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ = lean_array_mk(v_es_436_);
    return v___x_437_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(
    mut v_x1_438_: *mut crate::leanh::LeanObject,
    mut v_x2_439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_440_: u8 = 0;
    v___x_440_ = l_Lean_NameSet_contains(v_x1_438_, v_x2_439_);
    if v___x_440_ == 0 {
        let mut v___x_441_: u8 = 0;
        v___x_441_ = 1;
        return v___x_441_;
    } else {
        let mut v___x_442_: u8 = 0;
        v___x_442_ = 0;
        return v___x_442_;
    }
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(
    mut v_x1_443_: *mut crate::leanh::LeanObject,
    mut v_x2_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_445_: u8 = 0;
    let mut v_r_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_445_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x1_443_, v_x2_444_);
    crate::leanh::lean_dec(v_x2_444_);
    crate::leanh::lean_dec(v_x1_443_);
    v_r_446_ = crate::leanh::lean_box((v_res_445_) as usize);
    return v_r_446_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(
    mut v_hi_447_: *mut crate::leanh::LeanObject,
    mut v_pivot_448_: *mut crate::leanh::LeanObject,
    mut v_as_449_: *mut crate::leanh::LeanObject,
    mut v_i_450_: *mut crate::leanh::LeanObject,
    mut v_k_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_452_ = lean_nat_dec_lt(v_k_451_, v_hi_447_);
                if v___x_452_ == 0 {
                    crate::leanh::lean_dec(v_k_451_);
                    v___x_453_ = lean_array_fswap(v_as_449_, v_i_450_, v_hi_447_);
                    v___x_454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_454_, 0, v_i_450_);
                    crate::leanh::lean_ctor_set(v___x_454_, 1, v___x_453_);
                    return v___x_454_;
                } else {
                    v___x_455_ = lean_array_fget_borrowed(v_as_449_, v_k_451_);
                    v___x_456_ = l_Lean_Name_quickLt(v___x_455_, v_pivot_448_);
                    if v___x_456_ == 0 {
                        v___x_457_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_458_ = lean_nat_add(v_k_451_, v___x_457_);
                        crate::leanh::lean_dec(v_k_451_);
                        v_k_451_ = v___x_458_;
                        state = 0;
                        continue;
                    } else {
                        v___x_460_ = lean_array_fswap(v_as_449_, v_i_450_, v_k_451_);
                        v___x_461_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_462_ = lean_nat_add(v_i_450_, v___x_461_);
                        crate::leanh::lean_dec(v_i_450_);
                        v___x_463_ = lean_nat_add(v_k_451_, v___x_461_);
                        crate::leanh::lean_dec(v_k_451_);
                        v_as_449_ = v___x_460_;
                        v_i_450_ = v___x_462_;
                        v_k_451_ = v___x_463_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(
    mut v_hi_465_: *mut crate::leanh::LeanObject,
    mut v_pivot_466_: *mut crate::leanh::LeanObject,
    mut v_as_467_: *mut crate::leanh::LeanObject,
    mut v_i_468_: *mut crate::leanh::LeanObject,
    mut v_k_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_465_, v_pivot_466_, v_as_467_, v_i_468_, v_k_469_);
    crate::leanh::lean_dec(v_pivot_466_);
    crate::leanh::lean_dec(v_hi_465_);
    return v_res_470_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(
    mut v_n_471_: *mut crate::leanh::LeanObject,
    mut v_as_472_: *mut crate::leanh::LeanObject,
    mut v_lo_473_: *mut crate::leanh::LeanObject,
    mut v_hi_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u8 = 0;
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_486_ = lean_nat_dec_lt(v_lo_473_, v_hi_474_);
                if v___x_486_ == 0 {
                    crate::leanh::lean_dec(v_lo_473_);
                    return v_as_472_;
                } else {
                    v___x_487_ = lean_nat_add(v_lo_473_, v_hi_474_);
                    v___x_488_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_489_ = lean_nat_shiftr(v___x_487_, v___x_488_);
                    crate::leanh::lean_dec(v___x_487_);
                    v___x_502_ = lean_array_fget_borrowed(v_as_472_, v_mid_489_);
                    v___x_503_ = lean_array_fget_borrowed(v_as_472_, v_lo_473_);
                    v___x_504_ = l_Lean_Name_quickLt(v___x_502_, v___x_503_);
                    if v___x_504_ == 0 {
                        v___y_497_ = v_as_472_;
                        state = 3;
                        continue;
                    } else {
                        v___x_505_ = lean_array_fswap(v_as_472_, v_lo_473_, v_mid_489_);
                        v___y_497_ = v___x_505_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_477_ = lean_array_fget(v___y_476_, v_hi_474_);
                crate::leanh::lean_inc_n(v_lo_473_, 2);
                v___x_478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_474_, v_pivot_477_, v___y_476_, v_lo_473_, v_lo_473_);
                crate::leanh::lean_dec(v_pivot_477_);
                v_fst_479_ = crate::leanh::lean_ctor_get(v___x_478_, 0);
                crate::leanh::lean_inc(v_fst_479_);
                v_snd_480_ = crate::leanh::lean_ctor_get(v___x_478_, 1);
                crate::leanh::lean_inc(v_snd_480_);
                crate::leanh::lean_dec_ref(v___x_478_);
                v___x_481_ = lean_nat_dec_le(v_hi_474_, v_fst_479_);
                if v___x_481_ == 0 {
                    v___x_482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_471_, v_snd_480_, v_lo_473_, v_fst_479_);
                    v___x_483_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_484_ = lean_nat_add(v_fst_479_, v___x_483_);
                    crate::leanh::lean_dec(v_fst_479_);
                    v_as_472_ = v___x_482_;
                    v_lo_473_ = v___x_484_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_479_);
                    crate::leanh::lean_dec(v_lo_473_);
                    return v_snd_480_;
                }
            }
            2 => {
                v___x_492_ = lean_array_fget_borrowed(v___y_491_, v_mid_489_);
                v___x_493_ = lean_array_fget_borrowed(v___y_491_, v_hi_474_);
                v___x_494_ = l_Lean_Name_quickLt(v___x_492_, v___x_493_);
                if v___x_494_ == 0 {
                    crate::leanh::lean_dec(v_mid_489_);
                    v___y_476_ = v___y_491_;
                    state = 1;
                    continue;
                } else {
                    v___x_495_ = lean_array_fswap(v___y_491_, v_mid_489_, v_hi_474_);
                    crate::leanh::lean_dec(v_mid_489_);
                    v___y_476_ = v___x_495_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_498_ = lean_array_fget_borrowed(v___y_497_, v_hi_474_);
                v___x_499_ = lean_array_fget_borrowed(v___y_497_, v_lo_473_);
                v___x_500_ = l_Lean_Name_quickLt(v___x_498_, v___x_499_);
                if v___x_500_ == 0 {
                    v___y_491_ = v___y_497_;
                    state = 2;
                    continue;
                } else {
                    v___x_501_ = lean_array_fswap(v___y_497_, v_lo_473_, v_hi_474_);
                    v___y_491_ = v___x_501_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_n_506_: *mut crate::leanh::LeanObject,
    mut v_as_507_: *mut crate::leanh::LeanObject,
    mut v_lo_508_: *mut crate::leanh::LeanObject,
    mut v_hi_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_506_, v_as_507_, v_lo_508_, v_hi_509_);
    crate::leanh::lean_dec(v_hi_509_);
    crate::leanh::lean_dec(v_n_506_);
    return v_res_510_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(
    mut v_x_511_: *mut crate::leanh::LeanObject,
    mut v_x_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_512_) == 0 {
                    return v_x_511_;
                } else {
                    v_head_513_ = crate::leanh::lean_ctor_get(v_x_512_, 0);
                    crate::leanh::lean_inc(v_head_513_);
                    v_tail_514_ = crate::leanh::lean_ctor_get(v_x_512_, 1);
                    crate::leanh::lean_inc(v_tail_514_);
                    crate::leanh::lean_dec_ref_known(v_x_512_, 2);
                    v___x_515_ = lean_array_push(v_x_511_, v_head_513_);
                    v_x_511_ = v___x_515_;
                    v_x_512_ = v_tail_514_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(
    mut v___x_517_: *mut crate::leanh::LeanObject,
    mut v_env_518_: *mut crate::leanh::LeanObject,
    mut v_s_519_: *mut crate::leanh::LeanObject,
    mut v_entries_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u8 = 0;
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_521_ = lean_mk_empty_array_with_capacity(v___x_517_);
                crate::leanh::lean_inc_ref(v___x_521_);
                v_decls_522_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(v___x_521_, v_entries_520_);
                v___x_523_ = lean_array_get_size(v_decls_522_);
                v___x_529_ = lean_nat_dec_eq(v___x_523_, v___x_517_);
                if v___x_529_ == 0 {
                    v___x_530_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_531_ = lean_nat_sub(v___x_523_, v___x_530_);
                    v___x_535_ = lean_nat_dec_le(v___x_517_, v___x_531_);
                    if v___x_535_ == 0 {
                        crate::leanh::lean_dec(v___x_517_);
                        crate::leanh::lean_inc(v___x_531_);
                        v___y_533_ = v___x_531_;
                        state = 2;
                        continue;
                    } else {
                        v___y_533_ = v___x_517_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_517_);
                    crate::leanh::lean_inc_ref(v___x_521_);
                    v___x_536_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_521_);
                    crate::leanh::lean_ctor_set(v___x_536_, 1, v___x_521_);
                    crate::leanh::lean_ctor_set(v___x_536_, 2, v_decls_522_);
                    return v___x_536_;
                }
            }
            1 => {
                v___x_527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v___x_523_, v_decls_522_, v___y_525_, v___y_526_);
                crate::leanh::lean_dec(v___y_526_);
                crate::leanh::lean_inc_ref(v___x_521_);
                v___x_528_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_528_, 0, v___x_521_);
                crate::leanh::lean_ctor_set(v___x_528_, 1, v___x_521_);
                crate::leanh::lean_ctor_set(v___x_528_, 2, v___x_527_);
                return v___x_528_;
            }
            2 => {
                v___x_534_ = lean_nat_dec_le(v___y_533_, v___x_531_);
                if v___x_534_ == 0 {
                    crate::leanh::lean_dec(v___x_531_);
                    crate::leanh::lean_inc(v___y_533_);
                    v___y_525_ = v___y_533_;
                    v___y_526_ = v___y_533_;
                    state = 1;
                    continue;
                } else {
                    v___y_525_ = v___y_533_;
                    v___y_526_ = v___x_531_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(
    mut v___x_537_: *mut crate::leanh::LeanObject,
    mut v_env_538_: *mut crate::leanh::LeanObject,
    mut v_s_539_: *mut crate::leanh::LeanObject,
    mut v_entries_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v___x_537_, v_env_538_, v_s_539_, v_entries_540_);
    crate::leanh::lean_dec(v_s_539_);
    crate::leanh::lean_dec_ref(v_env_538_);
    return v_res_541_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_;
    v___x_569_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_568_);
    return v___x_569_;
}
pub unsafe fn l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(
    mut v_a_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
    return v_res_571_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(
    mut v_n_572_: *mut crate::leanh::LeanObject,
    mut v_as_573_: *mut crate::leanh::LeanObject,
    mut v_lo_574_: *mut crate::leanh::LeanObject,
    mut v_hi_575_: *mut crate::leanh::LeanObject,
    mut v_w_576_: *mut crate::leanh::LeanObject,
    mut v_hlo_577_: *mut crate::leanh::LeanObject,
    mut v_hhi_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_572_, v_as_573_, v_lo_574_, v_hi_575_);
    return v___x_579_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(
    mut v_n_580_: *mut crate::leanh::LeanObject,
    mut v_as_581_: *mut crate::leanh::LeanObject,
    mut v_lo_582_: *mut crate::leanh::LeanObject,
    mut v_hi_583_: *mut crate::leanh::LeanObject,
    mut v_w_584_: *mut crate::leanh::LeanObject,
    mut v_hlo_585_: *mut crate::leanh::LeanObject,
    mut v_hhi_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(v_n_580_, v_as_581_, v_lo_582_, v_hi_583_, v_w_584_, v_hlo_585_, v_hhi_586_);
    crate::leanh::lean_dec(v_hi_583_);
    crate::leanh::lean_dec(v_n_580_);
    return v_res_587_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(
    mut v_n_588_: *mut crate::leanh::LeanObject,
    mut v_lo_589_: *mut crate::leanh::LeanObject,
    mut v_hi_590_: *mut crate::leanh::LeanObject,
    mut v_hhi_591_: *mut crate::leanh::LeanObject,
    mut v_pivot_592_: *mut crate::leanh::LeanObject,
    mut v_as_593_: *mut crate::leanh::LeanObject,
    mut v_i_594_: *mut crate::leanh::LeanObject,
    mut v_k_595_: *mut crate::leanh::LeanObject,
    mut v_ilo_596_: *mut crate::leanh::LeanObject,
    mut v_ik_597_: *mut crate::leanh::LeanObject,
    mut v_w_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_590_, v_pivot_592_, v_as_593_, v_i_594_, v_k_595_);
    return v___x_599_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_n_600_: *mut crate::leanh::LeanObject,
    mut v_lo_601_: *mut crate::leanh::LeanObject,
    mut v_hi_602_: *mut crate::leanh::LeanObject,
    mut v_hhi_603_: *mut crate::leanh::LeanObject,
    mut v_pivot_604_: *mut crate::leanh::LeanObject,
    mut v_as_605_: *mut crate::leanh::LeanObject,
    mut v_i_606_: *mut crate::leanh::LeanObject,
    mut v_k_607_: *mut crate::leanh::LeanObject,
    mut v_ilo_608_: *mut crate::leanh::LeanObject,
    mut v_ik_609_: *mut crate::leanh::LeanObject,
    mut v_w_610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(v_n_600_, v_lo_601_, v_hi_602_, v_hhi_603_, v_pivot_604_, v_as_605_, v_i_606_, v_k_607_, v_ilo_608_, v_ik_609_, v_w_610_);
    crate::leanh::lean_dec(v_pivot_604_);
    crate::leanh::lean_dec(v_hi_602_);
    crate::leanh::lean_dec(v_lo_601_);
    crate::leanh::lean_dec(v_n_600_);
    return v_res_611_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(
    mut v___x_612_: u8,
    mut v_as_613_: *mut crate::leanh::LeanObject,
    mut v_k_614_: *mut crate::leanh::LeanObject,
    mut v_x_615_: *mut crate::leanh::LeanObject,
    mut v_x_616_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_617_ = lean_nat_add(v_x_615_, v_x_616_);
                v___x_618_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_619_ = lean_nat_shiftr(v___x_617_, v___x_618_);
                crate::leanh::lean_dec(v___x_617_);
                v_a_620_ = lean_array_fget_borrowed(v_as_613_, v_m_619_);
                v___x_621_ = l_Lean_Name_quickLt(v_a_620_, v_k_614_);
                if v___x_621_ == 0 {
                    crate::leanh::lean_dec(v_x_616_);
                    v___x_622_ = l_Lean_Name_quickLt(v_k_614_, v_a_620_);
                    if v___x_622_ == 0 {
                        crate::leanh::lean_dec(v_m_619_);
                        crate::leanh::lean_dec(v_x_615_);
                        return v___x_612_;
                    } else {
                        v___x_623_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_624_ = lean_nat_dec_eq(v_m_619_, v___x_623_);
                        if v___x_624_ == 0 {
                            v___x_625_ = lean_nat_sub(v_m_619_, v___x_618_);
                            crate::leanh::lean_dec(v_m_619_);
                            v___x_626_ = lean_nat_dec_lt(v___x_625_, v_x_615_);
                            if v___x_626_ == 0 {
                                v_x_616_ = v___x_625_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_625_);
                                crate::leanh::lean_dec(v_x_615_);
                                return v___x_621_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_619_);
                            crate::leanh::lean_dec(v_x_615_);
                            return v___x_621_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_615_);
                    v___x_628_ = lean_nat_add(v_m_619_, v___x_618_);
                    crate::leanh::lean_dec(v_m_619_);
                    v___x_629_ = lean_nat_dec_le(v___x_628_, v_x_616_);
                    if v___x_629_ == 0 {
                        crate::leanh::lean_dec(v___x_628_);
                        crate::leanh::lean_dec(v_x_616_);
                        return v___x_629_;
                    } else {
                        v_x_615_ = v___x_628_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(
    mut v___x_631_: *mut crate::leanh::LeanObject,
    mut v_as_632_: *mut crate::leanh::LeanObject,
    mut v_k_633_: *mut crate::leanh::LeanObject,
    mut v_x_634_: *mut crate::leanh::LeanObject,
    mut v_x_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_435__boxed_636_: u8 = 0;
    let mut v_res_637_: u8 = 0;
    let mut v_r_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_435__boxed_636_ = (crate::leanh::lean_unbox(v___x_631_) as u8);
    v_res_637_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(
        v___x_435__boxed_636_,
        v_as_632_,
        v_k_633_,
        v_x_634_,
        v_x_635_,
    );
    crate::leanh::lean_dec(v_k_633_);
    crate::leanh::lean_dec_ref(v_as_632_);
    v_r_638_ = crate::leanh::lean_box((v_res_637_) as usize);
    return v_r_638_;
}
pub unsafe fn l_Lean_isDeclMeta(
    mut v_env_643_: *mut crate::leanh::LeanObject,
    mut v_declName_644_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_646_: u8 = 0;
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v___y_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v_val_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: u8 = 0;
    let mut v_pre_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_645_ = l_Lean_Environment_header(v_env_643_);
                v_isModule_646_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_645_);
                if v_isModule_646_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_643_);
                    v___x_647_ = 1;
                    return v___x_647_;
                } else {
                    v___x_648_ = 0;
                    if crate::leanh::lean_obj_tag(v_declName_644_) == 1 {
                        v_pre_671_ = crate::leanh::lean_ctor_get(v_declName_644_, 0);
                        v_str_672_ = crate::leanh::lean_ctor_get(v_declName_644_, 1);
                        v___x_673_ = l_Lean_isDeclMeta___closed__1;
                        v___x_674_ = lean_string_dec_eq(v_str_672_, v___x_673_);
                        if v___x_674_ == 0 {
                            v___y_650_ = v_declName_644_;
                            state = 1;
                            continue;
                        } else {
                            v___y_650_ = v_pre_671_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_650_ = v_declName_644_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_651_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_643_, v_declName_644_);
                if crate::leanh::lean_obj_tag(v___x_651_) == 0 {
                    v___x_652_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
                    v_toEnvExtension_653_ = crate::leanh::lean_ctor_get(v___x_652_, 0);
                    v_asyncMode_654_ = crate::leanh::lean_ctor_get(v_toEnvExtension_653_, 2);
                    v___x_655_ = crate::leanh::lean_box(1);
                    v___x_656_ = crate::leanh::lean_box(0);
                    v___x_657_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_655_,
                        v___x_652_,
                        v_env_643_,
                        v_asyncMode_654_,
                        v___x_656_,
                    );
                    v___x_658_ = l_Lean_NameSet_contains(v___x_657_, v___y_650_);
                    crate::leanh::lean_dec(v___x_657_);
                    return v___x_658_;
                } else {
                    v_val_659_ = crate::leanh::lean_ctor_get(v___x_651_, 0);
                    crate::leanh::lean_inc(v_val_659_);
                    crate::leanh::lean_dec_ref_known(v___x_651_, 1);
                    v___x_660_ = l_Lean_isDeclMeta___closed__0;
                    v___x_661_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
                    v___x_662_ = 0;
                    v___x_663_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                        v___x_660_, v___x_661_, v_env_643_, v_val_659_, v___x_662_,
                    );
                    crate::leanh::lean_dec(v_val_659_);
                    crate::leanh::lean_dec_ref(v_env_643_);
                    v___x_664_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_665_ = lean_array_get_size(v___x_663_);
                    v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
                    if v___x_666_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_663_);
                        return v___x_648_;
                    } else {
                        v___x_667_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_668_ = lean_nat_sub(v___x_665_, v___x_667_);
                        v___x_669_ = lean_nat_dec_le(v___x_664_, v___x_668_);
                        if v___x_669_ == 0 {
                            crate::leanh::lean_dec(v___x_668_);
                            crate::leanh::lean_dec_ref(v___x_663_);
                            return v___x_648_;
                        } else {
                            v___x_670_ =
                                l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(
                                    v_isModule_646_,
                                    v___x_663_,
                                    v___y_650_,
                                    v___x_664_,
                                    v___x_668_,
                                );
                            crate::leanh::lean_dec_ref(v___x_663_);
                            return v___x_670_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isDeclMeta___boxed(
    mut v_env_675_: *mut crate::leanh::LeanObject,
    mut v_declName_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: u8 = 0;
    let mut v_r_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Lean_isDeclMeta(v_env_675_, v_declName_676_);
    crate::leanh::lean_dec(v_declName_676_);
    v_r_678_ = crate::leanh::lean_box((v_res_677_) as usize);
    return v_r_678_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(
    mut v___x_679_: u8,
    mut v_as_680_: *mut crate::leanh::LeanObject,
    mut v_k_681_: *mut crate::leanh::LeanObject,
    mut v_x_682_: *mut crate::leanh::LeanObject,
    mut v_x_683_: *mut crate::leanh::LeanObject,
    mut v_x_684_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_685_: u8 = 0;
    v___x_685_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(
        v___x_679_, v_as_680_, v_k_681_, v_x_682_, v_x_683_,
    );
    return v___x_685_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(
    mut v___x_686_: *mut crate::leanh::LeanObject,
    mut v_as_687_: *mut crate::leanh::LeanObject,
    mut v_k_688_: *mut crate::leanh::LeanObject,
    mut v_x_689_: *mut crate::leanh::LeanObject,
    mut v_x_690_: *mut crate::leanh::LeanObject,
    mut v_x_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_534__boxed_692_: u8 = 0;
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_534__boxed_692_ = (crate::leanh::lean_unbox(v___x_686_) as u8);
    v_res_693_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(
        v___x_534__boxed_692_,
        v_as_687_,
        v_k_688_,
        v_x_689_,
        v_x_690_,
        v_x_691_,
    );
    crate::leanh::lean_dec(v_k_688_);
    crate::leanh::lean_dec_ref(v_as_687_);
    v_r_694_ = crate::leanh::lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l_Lean_setDeclMeta(
    mut v_env_695_: *mut crate::leanh::LeanObject,
    mut v_declName_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_697_: u8 = 0;
    crate::leanh::lean_inc_ref(v_env_695_);
    v___x_697_ = l_Lean_isDeclMeta(v_env_695_, v_declName_696_);
    if v___x_697_ == 0 {
        let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_698_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
        v_toEnvExtension_699_ = crate::leanh::lean_ctor_get(v___x_698_, 0);
        v_asyncMode_700_ = crate::leanh::lean_ctor_get(v_toEnvExtension_699_, 2);
        v___x_701_ = crate::leanh::lean_box(0);
        v___x_702_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
            v___x_698_,
            v_env_695_,
            v_declName_696_,
            v_asyncMode_700_,
            v___x_701_,
        );
        return v___x_702_;
    } else {
        crate::leanh::lean_dec(v_declName_696_);
        return v_env_695_;
    }
}
pub unsafe fn l_panic___at___00Lean_getIRPhases_spec__0(
    mut v_msg_710_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: u8 = 0;
    v___f_711_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__0;
    v___f_712_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__1;
    v___f_713_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__2;
    v___f_714_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__3;
    v___f_715_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__4;
    v___f_716_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__5;
    v___f_717_ = l_panic___at___00Lean_getIRPhases_spec__0___closed__6;
    v___x_718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_718_, 0, v___f_711_);
    crate::leanh::lean_ctor_set(v___x_718_, 1, v___f_712_);
    v___x_719_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_719_, 0, v___x_718_);
    crate::leanh::lean_ctor_set(v___x_719_, 1, v___f_713_);
    crate::leanh::lean_ctor_set(v___x_719_, 2, v___f_714_);
    crate::leanh::lean_ctor_set(v___x_719_, 3, v___f_715_);
    crate::leanh::lean_ctor_set(v___x_719_, 4, v___f_716_);
    v___x_720_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_720_, 0, v___x_719_);
    crate::leanh::lean_ctor_set(v___x_720_, 1, v___f_717_);
    v___x_721_ = 0;
    v___x_722_ = crate::leanh::lean_box((v___x_721_) as usize);
    v___x_723_ = l_instInhabitedOfMonad___redArg(v___x_720_, v___x_722_);
    v___x_724_ = lean_panic_fn_borrowed(v___x_723_, v_msg_710_);
    crate::leanh::lean_dec(v___x_723_);
    v___x_725_ = (crate::leanh::lean_unbox(v___x_724_) as u8);
    crate::leanh::lean_dec(v___x_724_);
    return v___x_725_;
}
pub unsafe fn l_panic___at___00Lean_getIRPhases_spec__0___boxed(
    mut v_msg_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_727_: u8 = 0;
    let mut v_r_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_727_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_726_);
    v_r_728_ = crate::leanh::lean_box((v_res_727_) as usize);
    return v_r_728_;
}
pub unsafe fn _init_l_Lean_getIRPhases___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_getIRPhases___closed__2;
    v___x_733_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_734_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_735_ = l_Lean_getIRPhases___closed__1;
    v___x_736_ = l_Lean_getIRPhases___closed__0;
    v___x_737_ =
        l_mkPanicMessageWithDecl(v___x_736_, v___x_735_, v___x_734_, v___x_733_, v___x_732_);
    return v___x_737_;
}
pub unsafe fn l_Lean_getIRPhases(
    mut v_env_738_: *mut crate::leanh::LeanObject,
    mut v_declName_739_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_741_: u8 = 0;
    v___x_740_ = l_Lean_Environment_header(v_env_738_);
    v_isModule_741_ = crate::leanh::lean_ctor_get_uint8(
        v___x_740_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
    );
    if v_isModule_741_ == 0 {
        let mut v___x_742_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_740_);
        crate::leanh::lean_dec(v_declName_739_);
        crate::leanh::lean_dec_ref(v_env_738_);
        v___x_742_ = 2;
        return v___x_742_;
    } else {
        let mut v_modules_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_modules_743_ = crate::leanh::lean_ctor_get(v___x_740_, 3);
        crate::leanh::lean_inc_ref(v_modules_743_);
        crate::leanh::lean_dec_ref(v___x_740_);
        v___x_744_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_738_, v_declName_739_);
        if crate::leanh::lean_obj_tag(v___x_744_) == 0 {
            let mut v___x_745_: u8 = 0;
            let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_modules_743_);
            v___x_745_ = 0;
            crate::leanh::lean_inc(v_declName_739_);
            crate::leanh::lean_inc_ref(v_env_738_);
            v___x_746_ = l_Lean_Environment_find_x3f(v_env_738_, v_declName_739_, v___x_745_);
            if crate::leanh::lean_obj_tag(v___x_746_) == 0 {
                let mut v___x_747_: u8 = 0;
                crate::leanh::lean_dec(v_declName_739_);
                crate::leanh::lean_dec_ref(v_env_738_);
                v___x_747_ = 2;
                return v___x_747_;
            } else {
                let mut v_val_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_749_: u8 = 0;
                v_val_748_ = crate::leanh::lean_ctor_get(v___x_746_, 0);
                crate::leanh::lean_inc(v_val_748_);
                crate::leanh::lean_dec_ref_known(v___x_746_, 1);
                v___x_749_ = l_Lean_ConstantInfo_isCtor(v_val_748_);
                crate::leanh::lean_dec(v_val_748_);
                if v___x_749_ == 0 {
                    let mut v___x_750_: u8 = 0;
                    v___x_750_ = l_Lean_isMarkedMeta(v_env_738_, v_declName_739_);
                    if v___x_750_ == 0 {
                        let mut v___x_751_: u8 = 0;
                        v___x_751_ = 0;
                        return v___x_751_;
                    } else {
                        let mut v___x_752_: u8 = 0;
                        v___x_752_ = 1;
                        return v___x_752_;
                    }
                } else {
                    let mut v___x_753_: u8 = 0;
                    crate::leanh::lean_dec(v_declName_739_);
                    crate::leanh::lean_dec_ref(v_env_738_);
                    v___x_753_ = 2;
                    return v___x_753_;
                }
            }
        } else {
            let mut v_val_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_755_: u8 = 0;
            v_val_754_ = crate::leanh::lean_ctor_get(v___x_744_, 0);
            crate::leanh::lean_inc(v_val_754_);
            crate::leanh::lean_dec_ref_known(v___x_744_, 1);
            v___x_755_ = l_Lean_isMarkedMeta(v_env_738_, v_declName_739_);
            if v___x_755_ == 0 {
                let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_757_: u8 = 0;
                v___x_756_ = lean_array_get_size(v_modules_743_);
                v___x_757_ = lean_nat_dec_lt(v_val_754_, v___x_756_);
                if v___x_757_ == 0 {
                    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_759_: u8 = 0;
                    crate::leanh::lean_dec(v_val_754_);
                    crate::leanh::lean_dec_ref(v_modules_743_);
                    v___x_758_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_getIRPhases___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_getIRPhases___closed__3_once),
                        _init_l_Lean_getIRPhases___closed__3,
                    );
                    v___x_759_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_758_);
                    return v___x_759_;
                } else {
                    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_irPhases_761_: u8 = 0;
                    v___x_760_ = lean_array_fget(v_modules_743_, v_val_754_);
                    crate::leanh::lean_dec(v_val_754_);
                    crate::leanh::lean_dec_ref(v_modules_743_);
                    v_irPhases_761_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_760_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec(v___x_760_);
                    return v_irPhases_761_;
                }
            } else {
                let mut v___x_762_: u8 = 0;
                crate::leanh::lean_dec(v_val_754_);
                crate::leanh::lean_dec_ref(v_modules_743_);
                v___x_762_ = 1;
                return v___x_762_;
            }
        }
    }
}
pub unsafe fn l_Lean_getIRPhases___boxed(
    mut v_env_763_: *mut crate::leanh::LeanObject,
    mut v_declName_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Lean_getIRPhases(v_env_763_, v_declName_764_);
    v_r_766_ = crate::leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_MetaAttr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_MetaAttr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_MetaAttr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_MetaAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_MetaAttr(builtin);
}
